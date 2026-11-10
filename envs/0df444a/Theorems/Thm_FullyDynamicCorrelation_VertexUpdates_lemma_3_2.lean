-- Prove2me | Theorems.Thm_FullyDynamicCorrelation_VertexUpdates_lemma_3_2
-- name    : FullyDynamicCorrelation.VertexUpdates.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:55:09.555793+00:00
-- url     : https://prove2.me/theorems/0afd998e-5b96-44a2-a705-16c9e3449488
-- title:
--   Lemma 3.2 — merge into a cluster with a 4ε-dense core, or form an (ε/2)-almost-clique
-- statement:
--   For every $c>0$ there is $C>0$ such that for every $0<\varepsilon\le1/200$ there is a program with the following property. Let the maintained clusters be given by labels $\mathrm{lab}(u)$ ($0$: no cluster; cluster $\ell\ge1$ is $\{u\in V:\mathrm{lab}(u)=\ell\}$, with its size stored), and let $v\in V$ be $\varepsilon/20$-dense with $\mathrm{lab}(v)=0$. With probability at least $1-n^{-c}$ the program halts and either
--
--   - **merges** (cell $0$ = 1): it names an existing cluster $C$ (label in cell $5$), within $C\log_2^2n/\varepsilon^2$ instructions, and $C$ and $C\cup\{v\}$ each contain a $4\varepsilon$-almost-clique of size at least $(1-8\varepsilon)$ times their size, the latter containing $v$; or
--   - **forms** (cell $0$ = 2): it outputs, without repetition, a set $K$ within $C|K|\log_2^2n/\varepsilon^2$ instructions such that $v\in K$, $K$ is an $(\varepsilon/2)$-almost-clique, $(1-\varepsilon/20)|N[v]|\le|K|\le(1+0.051\varepsilon)|N[v]|$, $K$ contains every vertex in $(\varepsilon/5)$-agreement with $v$ and no $2\varepsilon$-sparse vertex, and if $\deg v<10/\varepsilon$ then $K=N[v]$ and $N[u]=K$ for all $u\in K$;
--
--   and it merges whenever $\deg v\ge10/\varepsilon$ and some cluster $C$ has $|N(v)\setminus C|<3\varepsilon\deg v$ and $|C|\le(1+4\varepsilon)\deg v$.
--
--   Differences from the source:
--   - encoding: an algorithm in the adjacency-list model with O(1)-time queries → a Program of the unit-cost RAM (RAM module): constants, +, truncated −, indirect access, jumps, degree / neighbour / edge queries and uniform random choice, one unit per executed instruction; reason: fixes the paper’s operation count; with no multiplication or division the machine is no stronger than the paper’s
--   - encoding: the graph G and its adjacency list → an SGraph whose vertex names are < n, presented by adjacency lists adj in arbitrary order (Presents); reason: the lists are given to the algorithm; their order is not under its control
--   - reading: “with high probability” → for every c > 0 there are constants and a program with failure probability at most n^(−c), for every n ≥ 2; reason: the standard meaning, made explicit by the amplification remark of p. 18 (log n → log(n/ξ))
--   - encoding: the maintained clusters and “adds v to an existing cluster C” → a labelling lab (0 = no cluster) with the cluster sizes stored in memory; a merge reports the label of C in cell 5; reason: input/output convention; the algorithm reads labels and sizes in O(1) as in the proof
--   - encoding: “C = N[v] is an isolated exact clique” → K = N[v] and N[u] = K for every u ∈ K; reason: every member is adjacent to all others and to nothing outside
--   - encoding: ε ≤ 1/200 → 0 < ε ≤ 1/200; reason: ε is an accuracy parameter; the time bound divides by ε²
--   - encoding: “in O(log² n/ε²) time” / “in O(|C| log² n/ε²) time” in the two branches → the run is given the allowance ⌊C(|V|+1) log₂² n/ε²⌋ and each branch bounds the number of instructions actually executed; reason: the larger allowance only makes the branch bounds observable; |C| ≤ |V|
-- source:
--   Braverman, Dharangutte, Fan, Wang, Xie and Zhou (2026), Fully Dynamic Correlation Clustering with Vertex Updates in Polylogarithmic Update Time, supplied manuscript sha256 07ee1c8f4214025e0b6a81ffc141dbcc4d3bc385abe36d5b298e3ec6037aaab2, Lemma 3.2, p. 16

import Mathlib
import Definitions.Def_FullyDynamicCorrelation_VertexUpdates_RAM

namespace FullyDynamicCorrelation.VertexUpdates

open Classical

/-- Lemma 3.2 (p. 16). -/
theorem lemma_3_2 :
    ∀ c : ℝ, 0 < c → ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 200 →
        ∃ P : Program,
          ∀ n : ℕ, 2 ≤ n → ∀ H : SGraph, (∀ v ∈ H.V, v < n) →
            ∀ adj : ℕ → List ℕ, Presents H adj →
              ∀ lab : ℕ → ℕ, (∀ u, lab u ≠ 0 → u ∈ H.V) →
                ∀ v ∈ H.V, lab v = 0 → ¬ H.Sparse (ε / 20) v →
                  1 - (n : ℝ) ^ (-c) ≤
                    ((runCall P H adj
                        (inputMem n v [] lab (fun l => (H.V.filter (fun u => lab u = l)).card))
                        ⌊C * ((H.V.card : ℝ) + 1) * lg n ^ 2 / ε ^ 2⌋₊).toOuterMeasure
                      {o | ∃ (m : ℕ → ℕ) (st : ℕ), o = some (m, st) ∧
                        ((m 0 = 1 ∧ 1 ≤ m 5 ∧ (H.V.filter (fun u => lab u = m 5)).Nonempty ∧
                            (st : ℝ) ≤ C * lg n ^ 2 / ε ^ 2 ∧
                            (∃ K ⊆ H.V.filter (fun u => lab u = m 5),
                              H.IsAlmostClique (4 * ε) K ∧
                              (1 - 8 * ε) * ((H.V.filter (fun u => lab u = m 5)).card : ℝ) ≤
                                (K.card : ℝ)) ∧
                            (∃ K ⊆ insert v (H.V.filter (fun u => lab u = m 5)), v ∈ K ∧
                              H.IsAlmostClique (4 * ε) K ∧
                              (1 - 8 * ε) *
                                  ((insert v (H.V.filter (fun u => lab u = m 5))).card : ℝ) ≤
                                (K.card : ℝ))) ∨
                         (m 0 = 2 ∧ (outputList m).Nodup ∧
                            (st : ℝ) ≤ C * ((outputList m).length : ℝ) * lg n ^ 2 / ε ^ 2 ∧
                            v ∈ (outputList m).toFinset ∧
                            H.IsAlmostClique (ε / 2) (outputList m).toFinset ∧
                            (1 - ε / 20) * ((H.cnbr v).card : ℝ) ≤ ((outputList m).length : ℝ) ∧
                            ((outputList m).length : ℝ) ≤
                              (1 + (51 / 1000) * ε) * ((H.cnbr v).card : ℝ) ∧
                            (∀ u ∈ H.V, H.Agree (ε / 5) u v → u ∈ (outputList m).toFinset) ∧
                            (∀ u ∈ (outputList m).toFinset, ¬ H.Sparse (2 * ε) u) ∧
                            ((H.deg v : ℝ) < 10 / ε →
                              (outputList m).toFinset = H.cnbr v ∧
                                ∀ u ∈ (outputList m).toFinset,
                                  H.cnbr u = (outputList m).toFinset))) ∧
                        ((10 / ε ≤ (H.deg v : ℝ) ∧
                            ∃ l, 1 ≤ l ∧ (H.V.filter (fun u => lab u = l)).Nonempty ∧
                              (((H.nbr v \ H.V.filter (fun u => lab u = l)).card : ℕ) : ℝ) <
                                3 * ε * (H.deg v : ℝ) ∧
                              ((H.V.filter (fun u => lab u = l)).card : ℝ) ≤
                                (1 + 4 * ε) * (H.deg v : ℝ)) → m 0 = 1)}).toReal := by sorry

end FullyDynamicCorrelation.VertexUpdates
