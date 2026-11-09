-- Prove2me | Theorems.Thm_HypClass1_lemma_7_1
-- name    : HypClass1.lemma_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:35:04.167204+00:00
-- url     : https://prove2.me/theorems/c89a9563-07c4-4b32-bc7d-e0e4ac715fdb
-- title:
--   Lemma 7.1 (Stage I) — reducing the density of the remainder
-- statement:
--   Let $C$ be a sufficiently large constant and $n$ a sufficiently large integer. Let $\varepsilon, \delta, \lambda, p, r \in [0,1]$ satisfy
--   $$
--   n^{-1/5} \le \varepsilon \le \delta \le C^{-3}, \qquad \frac{C\log n}{\varepsilon^2 n} \le r \le p, \qquad C\varepsilon^2\log n \le \delta^6, \qquad Cn^{-1} \le \lambda .
--   $$
--   Let $S \subseteq [n]$ with $|S| = n/100$. Let $H$ and $R$ be edge-disjoint 3-graphs on $[n]$ such that $H$ is $(\varepsilon,p,n)$-pseudorandom, $\deg_R(u,v) = (1\pm\delta)rn$ for every pair $u \ne v$, and $\deg_H(u) = pn^2/2 \pm \lambda n^2$, $\deg_R(u) = rn^2/2 \pm \lambda n^2$ for every vertex $u$. Then there is a collection $\mathcal K$ of edge-disjoint matchings in $H \cup R$ with:
--   1. (F1) $R \subseteq \bigcup_{K\in\mathcal K} K \subseteq H \cup R$;
--   2. (F2) $[n] \setminus V(K) \subseteq S$ for every $K \in \mathcal K$;
--   3. (F3) every $u \in S$ is missed by at most $Cpn$ matchings of $\mathcal K$;
--   4. (F4) for $\tilde R = H \setminus \bigcup_{K\in\mathcal K} K$ there is a constant $c_\star > 0$, bounded above and below by functions of $C$, with $\deg_{\tilde R}(u) = c_\star\delta p n^2 \pm 5\lambda n^2$ for every $u$, and $\Delta_2(\tilde R) \le C^3\delta pn$.
--
--   Moreover, the same statement holds with $R = \emptyset$.
--
--   **Formalization Note** The lower and upper bounding functions of $c_\star$ are fixed before $C$; $a = b \pm c$ means $|a - b| \le c$. The case $R = \emptyset$ is a second conjunct in which every hypothesis on $R$ and $r$ is removed, except the bound $C\log n/(\varepsilon^2 n) \le p$ that the chain $C\log n/(\varepsilon^2 n) \le r \le p$ places on $p$.
--
--   Differences from the source:
--   - reading: 'for a sufficiently large constant C' (and integer n) → ∃ C₀, ∀ C ≥ C₀ (then ∃ n₀, ∀ n ≥ n₀ where the source says n is large); reason: the standard reading, and the way the paper applies these results ('Let C be a constant larger than all the previous constants', p.31)
--   - reading: |S| = n/100 → S.card = n / 100 in ℕ, i.e. ⌊n/100⌋; reason: the real equation is unsatisfiable unless 100 ∣ n, which would make the lemma vacuous for most n, while the paper applies it for every n (Prop 9.5, p.50)
--   - reading: 'a positive constant c⋆ bounded both above and below by a function of C' → ∃ lo hi : ℝ → ℝ before C, and in the conclusion ∃ c⋆ with 0 < lo C ≤ c⋆ ≤ hi C; reason: the bounding functions do not depend on n or the parameters
--   - reading: 'Moreover, the same statement holds if we take R = ∅' → a second conjunct for R = ∅ with the hypotheses on R and r removed, keeping C log n/(ε²n) ≤ p; reason: with R = ∅ the hypotheses on R and r cannot hold ((1 − δ)rn ≤ deg_R(u, v) = 0 forces r = 0, contradicting C log n/(ε²n) ≤ r); the proof treats R = ∅ as the case r = 0 and otherwise runs unchanged (p.26), using p ≥ C log n/(ε²n) for H (Lemma 5.2); the paper applies the case in the first round of Lemma 9.2 (p.54), where that bound holds
--   - encoding: a collection of edge disjoint matchings K → a Finset of pairwise edge-disjoint matchings; reason: by the property that [n] ∖ V(K) ⊆ S with |S| < n every matching is non-empty, and distinct non-empty edge-disjoint matchings cannot repeat, so no multiplicity is lost
--   - reading: log (base not named) → natural logarithm Real.log; reason: standard convention; paper.md decision 6
-- source:
--   Chatterjee, Ferber, Sales, Shurman, Almost Every 3-Uniform Hypergraph is Class 1, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), Lemma 7.1, p.25

import Mathlib
import Definitions.Def_HypClass1_K3
import Definitions.Def_HypClass1_deg
import Definitions.Def_HypClass1_codeg
import Definitions.Def_HypClass1_maxCodeg
import Definitions.Def_HypClass1_IsMatching
import Definitions.Def_HypClass1_IsPseudorandom3

namespace HypClass1

/-- **Lemma 7.1 (Stage I).** Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), Lemma 7.1, p.25:
"Let ε, δ, λ, p, r ∈ [0, 1] be real numbers and let n be a sufficiently large integer such that
n^{−1/5} ≤ ε ≤ δ ≤ C^{−3}, C log n/(ε²n) ≤ r ≤ p, Cε² log n ≤ δ⁶, and Cn^{−1} ≤ λ. Let S ⊆ [n] be a set
with |S| = n/100. Let H and R be edge-disjoint 3-graphs on [n] such that H is (ε, p, n)-pseudorandom
and deg_R(u, v) = (1 ± δ)rn for every pair {u, v} ⊆ [n]. Moreover, suppose that the degrees of both H
and R satisfy deg_H(u) = pn²/2 ± λn² and deg_R(u) = rn²/2 ± λn² for every vertex u ∈ [n]. Then there
exists a collection of edge disjoint matchings K in H ∪ R such that the following properties hold:
(F1) The collection K covers R, i.e., R ⊆ ⋃_{K∈K} K ⊆ H ∪ R.
(F2) For every K ∈ K, we have [n] ∖ V(K) ⊆ S.
(F3) For every u ∈ S, the number of matchings K ∈ K missing the vertex u is at most Cpn.
(F4) Let R̃ := H ∖ ⋃_{K∈K} K. Then there exists a positive constant c⋆ bounded both above and below by
a function of C such that deg_R̃(u) = c⋆δpn² ± 5λn² and ∆₂(R̃) ≤ C³δpn, for u ∈ [n].
Moreover, the same statement holds if we take R = ∅."

**Formalization Note.** "For a sufficiently large C" (the `C` of the hypotheses, cf. p.31) and
"n sufficiently large": `∃ C₀, ∀ C ≥ C₀, ∃ n₀, ∀ n ≥ n₀`. The bounding functions `lo, hi` of `c⋆` are
fixed before `C`, with `0 < lo C ≤ c⋆ ≤ hi C`. `|S| = n/100` is natural-number division (`⌊n/100⌋`).
`a = b ± c` means `|a − b| ≤ c`. The collection `K` is a finite set of pairwise edge-disjoint matchings
contained in `H ∪ R`. The "Moreover" clause is the second conjunct: the case `R = ∅`, with every
hypothesis on `R` and `r` removed except the bound `C log n/(ε²n) ≤ p` that the chain
`C log n/(ε²n) ≤ r ≤ p` places on `p` (the proof applies Lemma 5.2 to `H` with it, p.26, "the remainder of
the proof works whether R is dense or empty without changing a sentence"). -/
theorem lemma_7_1 :
    ∃ lo hi : ℝ → ℝ, ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (∀ ε δ lam p r : ℝ, 0 ≤ ε → ε ≤ 1 → 0 ≤ δ → δ ≤ 1 → 0 ≤ lam → lam ≤ 1 → 0 ≤ p → p ≤ 1 →
        0 ≤ r → r ≤ 1 →
        (n : ℝ) ^ (-(1 / 5 : ℝ)) ≤ ε → ε ≤ δ → δ ≤ C ^ (-3 : ℝ) →
        C * Real.log n / (ε ^ 2 * n) ≤ r → r ≤ p → C * ε ^ 2 * Real.log n ≤ δ ^ 6 →
        C * (n : ℝ)⁻¹ ≤ lam →
        ∀ S : Finset (Fin n), S.card = n / 100 →
        ∀ H R : Finset (Finset (Fin n)), H ⊆ K3 (Fin n) → R ⊆ K3 (Fin n) → Disjoint H R →
        IsPseudorandom3 ε p Finset.univ H →
        (∀ u v : Fin n, u ≠ v →
          (1 - δ) * r * n ≤ codeg R u v ∧ (codeg R u v : ℝ) ≤ (1 + δ) * r * n) →
        (∀ u : Fin n, |(deg H u : ℝ) - p * n ^ 2 / 2| ≤ lam * n ^ 2) →
        (∀ u : Fin n, |(deg R u : ℝ) - r * n ^ 2 / 2| ≤ lam * n ^ 2) →
        ∃ 𝒦 : Finset (Finset (Finset (Fin n))),
          (∀ K ∈ 𝒦, K ⊆ H ∪ R ∧ IsMatching K) ∧
          (∀ K ∈ 𝒦, ∀ K' ∈ 𝒦, K ≠ K' → Disjoint K K') ∧
          R ⊆ 𝒦.biUnion id ∧
          (∀ K ∈ 𝒦, Finset.univ \ verts K ⊆ S) ∧
          (∀ u ∈ S, ((𝒦.filter (fun K => u ∉ verts K)).card : ℝ) ≤ C * p * n) ∧
          ∃ cs : ℝ, 0 < lo C ∧ lo C ≤ cs ∧ cs ≤ hi C ∧
            (∀ u : Fin n,
              |(deg (H \ 𝒦.biUnion id) u : ℝ) - cs * δ * p * n ^ 2| ≤ 5 * lam * n ^ 2) ∧
            (maxCodeg (H \ 𝒦.biUnion id) : ℝ) ≤ C ^ 3 * δ * p * n) ∧
      (∀ ε δ lam p : ℝ, 0 ≤ ε → ε ≤ 1 → 0 ≤ δ → δ ≤ 1 → 0 ≤ lam → lam ≤ 1 → 0 ≤ p → p ≤ 1 →
        (n : ℝ) ^ (-(1 / 5 : ℝ)) ≤ ε → ε ≤ δ → δ ≤ C ^ (-3 : ℝ) →
        C * Real.log n / (ε ^ 2 * n) ≤ p → C * ε ^ 2 * Real.log n ≤ δ ^ 6 → C * (n : ℝ)⁻¹ ≤ lam →
        ∀ S : Finset (Fin n), S.card = n / 100 →
        ∀ H : Finset (Finset (Fin n)), H ⊆ K3 (Fin n) →
        IsPseudorandom3 ε p Finset.univ H →
        (∀ u : Fin n, |(deg H u : ℝ) - p * n ^ 2 / 2| ≤ lam * n ^ 2) →
        ∃ 𝒦 : Finset (Finset (Finset (Fin n))),
          (∀ K ∈ 𝒦, K ⊆ H ∧ IsMatching K) ∧
          (∀ K ∈ 𝒦, ∀ K' ∈ 𝒦, K ≠ K' → Disjoint K K') ∧
          (∀ K ∈ 𝒦, Finset.univ \ verts K ⊆ S) ∧
          (∀ u ∈ S, ((𝒦.filter (fun K => u ∉ verts K)).card : ℝ) ≤ C * p * n) ∧
          ∃ cs : ℝ, 0 < lo C ∧ lo C ≤ cs ∧ cs ≤ hi C ∧
            (∀ u : Fin n,
              |(deg (H \ 𝒦.biUnion id) u : ℝ) - cs * δ * p * n ^ 2| ≤ 5 * lam * n ^ 2) ∧
            (maxCodeg (H \ 𝒦.biUnion id) : ℝ) ≤ C ^ 3 * δ * p * n) := by sorry

end HypClass1
