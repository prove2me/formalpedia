-- Prove2me | Theorems.Thm_NewtonLCP_lemma_8_5
-- name    : NewtonLCP.lemma_8_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:29:48.234867+00:00
-- url     : https://prove2.me/theorems/9f133bb9-73b7-4756-b614-d6336c7fb23c
-- title:
--   Lemma 8.5 — recovering an exact solution from an approximate one
-- statement:
--   Let $M\in\mathbb R^{n\times n}$, $q\in\mathbb R^n$, $\kappa>0$, and let $\Delta$ be a bit bound for $(M,q)$ as in Lemma 8.3. Consider the embedded system LCP$(\widehat M,\hat q)$ of (52), let $((x,\tilde x),(s,\tilde s),\mu)\in\mathcal N^2(1/2)$ for it, with $\mu\le1/(16384n^3\Delta^2(\kappa+1)^2)$, and define
--
--   $$I=\{i\in[n]:x_i\le\sqrt{2n\mu}\},\qquad J=\{j\in[n]:s_j\le\sqrt{2n\mu}\}.$$
--
--   Then $I\cup J=[n]$, and at least one of the following holds:
--
--   1. there is a solution $(\bar x,\bar s)\in\mathcal F(M,q)$ with $\bar x_I=0_I$ and $\bar s_J=0_J$, which is a complementary solution of LCP$(M,q)$;
--   2. LCP$(M,q)$ has no solution;
--   3. $\hat\kappa(M)>\kappa$.
--
--   Algorithm 3 uses this to turn the output of FixedKappaNewton into an exact solution with one LP call.
--
--   **Formalization Note** "$\hat\kappa(M)>\kappa$" is $M\notin\mathcal P_\star(\kappa)$, which includes $M\notin\mathcal P_\star$ (where $\hat\kappa=\infty$).
--
--   Differences from the source:
--   - generalization: M ∈ ℚ^{n×n}, q ∈ ℚⁿ, Δ ≤ 2^{O(L)} as in Lemma 8.3 → real M, q and any integer Δ with the bit-bound property (IsBitBound); reason: the proof uses only the bit-bound property of Δ; rational data with Lemma 8.3's Δ satisfy it
--   - reading: (ii) LCP(M, q) is infeasible → LCP(M, q) has no (complementary) solution; reason: the proof's dichotomy is 'LCP(M, q) is feasible', i.e. has a complementary solution, from which it derives (i); not a weaker reading, since when (iii) fails, M ∈ P⋆ is row sufficient (Theorem 2.3) and Theorem 2.1 makes 'no complementary solution' equivalent to F(M, q) = ∅, so the disjunction is the same under either reading
--   - encoding: (iii) κ̂(M) > κ → ¬ IsPStarK M κ; reason: the paper sets κ̂(M) = ∞ off P⋆, so κ̂(M) > κ is exactly M ∉ P⋆(κ)
--   - encoding: n arbitrary → at n = 0 the bound µ ≤ 1/(16384·0·…) reads µ ≤ 0 and contradicts µ > 0, so the statement is vacuous; reason: the printed bound divides by n³ and is undefined at n = 0
-- source:
--   Ma–Végh–Vladu, Newton Steps are Faster for Linear Complementarity Problems, STOC 2027 submission (manuscript sha256 a70e5eab…), Lemma 8.5, p.30

import Mathlib
import Definitions.Def_NewtonLCP_Handicap
import Definitions.Def_NewtonLCP_Centrality
import Definitions.Def_NewtonLCP_BitBound
import Definitions.Def_NewtonLCP_Embedding

namespace NewtonLCP

/-- **Lemma 8.5** (identifying the optimal support). Ma–Végh–Vladu, *Newton Steps are Faster for Linear Complementarity Problems*, STOC 2027
submission manuscript (sha256 a70e5eab52f43bef42b49a8833f8d0483556c18b939405dba6bc1e25ea0740f8), Lemma 8.5, p.30.

Let `M ∈ ℚⁿˣⁿ`, `q ∈ ℚⁿ`, `κ > 0`, `L` the total encoding length of `(M, q)` and `∆ ≤ 2^{O(L)}`
as in Lemma 8.3. Consider the embedded system LCP(M̂, q̂) with `q̃` as in (52), let
`((x, x̃), (s, s̃), µ) ∈ N²(1/2)` and `µ ≤ 1/(16384n³∆²(κ+1)²)`. Define
`I = {i : xᵢ ≤ √(2nµ)}`, `J = {j : sⱼ ≤ √(2nµ)}`. Then `I ∪ J = [n]`, and at least one of the
following holds: (i) there is a solution `(x̄, s̄) ∈ F(M, q)` with `x̄_I = 0_I`, `s̄_J = 0_J`,
which is a complementary solution to LCP(M, q); (ii) LCP(M, q) is infeasible; (iii) `κ̂(M) > κ`.

**Formalization Note.** `M, q` real and `∆` any integer with `IsBitBound` (the paper's rational
data and Lemma 8.3's `∆` are a special case). "LCP(M, q) is infeasible" means it has no solution
(the proof's "LCP(M, q) is feasible" is the existence of a complementary solution).
"`κ̂(M) > κ`" is `¬ IsPStarK M κ` (it includes `M ∉ P⋆`, where `κ̂(M) = ∞`). `n = Fintype.card ι`;
at `n = 0` the bound on `µ` reads `µ ≤ 0` and the statement is vacuous. -/
theorem lemma_8_5 {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (q : ι → ℝ)
    (κ : ℝ) (hκ : 0 < κ) (Δ : ℤ) (hΔ : IsBitBound M q Δ) (x xt s st : ι → ℝ) (mu : ℝ)
    (hN : InN2 (embedM M) (embedQ M q Δ) (1 / 2) (Sum.elim x xt) (Sum.elim s st) mu)
    (hmu : mu ≤ 1 / (16384 * (Fintype.card ι : ℝ) ^ 3 * (Δ : ℝ) ^ 2 * (κ + 1) ^ 2)) :
    let I := Finset.univ.filter (fun i => x i ≤ Real.sqrt (2 * Fintype.card ι * mu))
    let J := Finset.univ.filter (fun j => s j ≤ Real.sqrt (2 * Fintype.card ι * mu))
    I ∪ J = Finset.univ ∧
      ((∃ xb sb : ι → ℝ, (xb, sb) ∈ Feas M q ∧ (∀ i ∈ I, xb i = 0) ∧ (∀ j ∈ J, sb j = 0) ∧
          IsLCPSol M q xb sb) ∨
        (¬ ∃ x s, IsLCPSol M q x s) ∨
        ¬ IsPStarK M κ) := by sorry

end NewtonLCP
