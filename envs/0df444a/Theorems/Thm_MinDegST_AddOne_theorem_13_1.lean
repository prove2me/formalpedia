-- Prove2me | Theorems.Thm_MinDegST_AddOne_theorem_13_1
-- name    : MinDegST.AddOne.theorem_13_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:53:11.865464+00:00
-- url     : https://prove2.me/theorems/2e7d1731-8bb8-446f-9c51-8747be9378cf
-- title:
--   Theorem 13.1 — Ω(f²/n) fewer components of a feasible forest in Ô(m) time
-- statement:
--   There are one deterministic word-RAM program, a word-width constant and a universal constant $c>0$, fixed before $\varepsilon$, such that for every $\varepsilon>0$ there is $K_\varepsilon>0$ with: for every connected graph $G$ with $n$ nodes and $m$ edges, threshold $k<n$ for which $G$ has a spanning tree of maximum degree at most $k$, and forest $F$ of $G$ of maximum degree at most $k+1$ with $f\ge2$ components, on input $(G,k,F)$ the program halts within $K_\varepsilon\cdot m\cdot n^{\varepsilon}+K_\varepsilon$ steps and outputs a forest $F'$ of $G$ of maximum degree at most $k+1$ whose number of components $f'$ satisfies
--   $$f-f'\ \ge\ c\cdot\frac{f^2}{n}.$$
--   This is the main subroutine: $O(\sqrt n)$ calls bring $f$ below $\lceil\sqrt n\rceil$, after which Lemma 13.2 finishes (proof of Theorem 1.1, p. 35).
--
--   Differences from the source:
--   - generalization: the degree bound is Δ⋆(G) (feasible = max degree ≤ Δ⋆ + 1, slack = degree ≤ Δ⋆, saturated = Δ⋆ + 1) → any threshold k < n for which G has a spanning tree of maximum degree ≤ k, with feasible/slack/saturated relative to k; reason: Part I's convention (p. 4); the case k = Δ⋆(G) is the source's statement (G connected has a spanning tree of maximum degree Δ⋆ ≤ n − 1)
--   - encoding: a deterministic algorithm (no machine model fixed) → one program of the CongruencyTU integer RAM (unit cost, no coin or query instruction), with one width constant fixed with the program bounding every register at every step by width·(1 + ⌊log₂(2 + scale)⌋) bits; reason: the paper fixes no machine; logarithmic words keep unit-cost arithmetic from trivializing running times; the external max-flow goal is stated on the same machine
--   - encoding: Ô(m) (subpolynomial factors in n hidden, footnote 8) → one program fixed first; ∀ ε > 0 ∃ K_ε > 0: cost ≤ K_ε·m·n^ε + K_ε; reason: the standard reading of n^{o(1)} factors with explicit constants
--   - encoding: given a feasible forest of G; compute augmenting chains → input [n, m, G's edge list, k, |E(F)|, F's edge list] in any order and orientation; output encMolecules lM ++ encFamily l𝓡 ++ encChains lA; reason: the output specifies the decomposition, its regions and the distinct node-sequence chains; it is not a new forest
--   - encoding: Ω(f²/n) fewer components → one universal c > 0, fixed with the program before ε: f − f' ≥ c·f²/n; reason: explicit constant for Ω; since f − f' is an integer this forces at least one merge
-- source:
--   Bhattacharya, Farokhnejad, Saranurak, Wang, Faster Algorithms for Minimum Degree Spanning Tree, STOC 2027 submission (manuscript sha256 7d985d3b…), p. 35, Theorem 13.1

import Mathlib
import Definitions.Def_CongruencyTU_Machine
import Definitions.Def_MinDegST_AddOne_Graph
import Definitions.Def_MinDegST_AddOne_Machine

namespace MinDegST.AddOne

/-- **Theorem 13.1** (threshold form). One deterministic word-RAM program, a word-width constant and
a universal constant `c > 0`, fixed before `ε`, such that for every `ε > 0` there is `K_ε > 0`
with: for every connected simple graph `G` on `Fin n` (edge list `es`, `m = |es|`), every threshold
`k < n` for which `G` has a spanning tree of maximum degree `≤ k`, and every forest `F` of `G` with
maximum degree `≤ k + 1` and `f ≥ 2` components (edge list `fs`), the program halts on
`(es, k, fs)` within `K_ε · m · n^ε + K_ε` steps and outputs the edges of a forest `F'` of `G` of
maximum degree `≤ k + 1` with `f − f' ≥ c · f² / n`, where `f'` is its number of components. -/
theorem theorem_13_1 :
    ∃ (P : CongruencyTU.Program) (width : ℕ) (c : ℝ), Deterministic P ∧ 0 < c ∧
      (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (es : List (Fin n × Fin n)) (k : ℕ)
        (F : SimpleGraph (Fin n)) (fs : List (Fin n × Fin n)),
        G.Connected → IsEdgeListOf G es → HasSpanningTreeLE G k → k < n →
        IsForestOf G F → Feasible k F → IsEdgeListOf F fs → 2 ≤ numComponents F →
          WordBounded P (encForestInput n es k fs) width (n + es.length)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (es : List (Fin n × Fin n)) (k : ℕ)
          (F : SimpleGraph (Fin n)) (fs : List (Fin n × Fin n)),
          G.Connected → IsEdgeListOf G es → HasSpanningTreeLE G k → k < n →
          IsForestOf G F → Feasible k F → IsEdgeListOf F fs → 2 ≤ numComponents F →
            HaltsWithin P (encForestInput n es k fs)
              (K * (es.length : ℝ) * (n : ℝ) ^ ε + K)
              (fun out => ∃ F' : SimpleGraph (Fin n), EncodesEdges out F' ∧
                IsForestOf G F' ∧ Feasible k F' ∧
                c * (numComponents F : ℝ) ^ 2 / n ≤
                  (numComponents F : ℝ) - (numComponents F' : ℝ)) := by sorry

end MinDegST.AddOne
