-- Prove2me | Theorems.Thm_NNPartTree_lemma_5_4
-- name    : NNPartTree.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:09:42.79922+00:00
-- url     : https://prove2.me/theorems/cd4bc8ac-fe9f-4de2-b4a7-27bba9e6964a
-- title:
--   Lemma 5.4, p.17 — a polynomial $A^\star$ of degree $k(\varepsilon)$ with $R_D\le(108/\beta)(\mathrm{err}(f)+\varepsilon)$ and $\gamma\le 6480/\beta^2$
-- statement:
--   Let $\beta\in(0,1/2]$ and $\varepsilon\in(0,\beta/8)$. Let $f$ be a cut with $\mathrm{bal}_{\mathcal D}(f)\ge\beta$, and suppose a polynomial of degree at most $k$ approximates $f$ to $\varepsilon$. Then there is a polynomial $A^\star$ of degree at most $k$, with positive variance on $\mathcal D_Y$ and finite moments, with
--   $$R_{\mathcal D}(A^\star)\le\frac{108}{\beta}\big(\mathrm{err}_{\mathcal D}(f)+\varepsilon\big)\quad\text{and}\quad\gamma(A^\star;\mathcal D_Y)\le\frac{6480}{\beta^2}.$$
--
--   Taking $f$ optimal gives the printed bound with $\mathrm{OPT}_\beta(\mathcal F)$. This is the existence step of the improper learner: a good cut yields a low-degree polynomial feasible for the program $\Pi$.
--
--   Differences from the source:
--   - generalization: F with approximation degree k(·), bound with OPT_β(F) → each f with bal(f) ≥ β approximated at ε, bound with err(f); reason: the proof fixes one such f; the printed form follows for an optimal f, and this form does not need the minimum to exist
--   - encoding: O(1/β), O(1/β²) → constants 108 and 6480; reason: the constants of the proof, p.46
--   - encoding: conclusion on R and γ → also positive variance and finite moments of A★; reason: R and γ are 0 in Lean otherwise, and the proof gives both
-- source:
--   Khanna, Padaki, Waingarten, Learning Partition Trees for Nearest Neighbor Search, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…), Lemma 5.4, p.17; proof pp.45–46, constants p.46

import Mathlib
import Definitions.Def_NNPartTree_Moments

open MeasureTheory

namespace NNPartTree

/-- **Lemma 5.4** (Low-Energy and Kurtosis Polynomial), p.17; proof pp.45–46. S. Khanna, A. Padaki, E. Waingarten, *Learning Partition Trees for Nearest Neighbor Search*, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…).

For `β ∈ (0, 1/2]` and `ε ∈ (0, β/8)` and any cut `f` with `bal_D(f) ≥ β` approximated to `ε` by degree `k`,
there is a polynomial `A★` of degree at most `k` with `R_D(A★) ≤ (108/β)(err_D(f) + ε)` and
`γ(A★; D_Y) ≤ 6480/β²`. The constants are those of the proof (p.46).

**Formalization Note.** Stated for each `f`, with `k = k(ε)`. Taking `f` optimal gives the printed form with
`OPT_β(F)`, and this form does not need the minimum to exist. The variance and finite moments of `A★`
are part of the conclusion, because `R` and `γ` are `0` in Lean otherwise. -/
theorem lemma_5_4 {d : ℕ} (D : Measure (Pt d × Pt d)) [IsProbabilityMeasure D] (β ε : ℝ)
    (hβ0 : 0 < β) (hβ : β ≤ 1 / 2) (hε0 : 0 < ε) (hε : ε < β / 8) (f : Pt d → ℝ) (hf : IsCut f)
    (k : ℕ) (hbal : β ≤ bal D f) (happ : ApproxAt D f ε k) :
    ∃ A : MvPolynomial (Fin d) ℝ, A.totalDegree ≤ k ∧ HasFiniteMoments D (peval A) ∧
      0 < varOn (marginalY D) (peval A) ∧
      energy D (peval A) ≤ 108 / β * (err D f + ε) ∧
      kurtosis (marginalY D) (peval A) ≤ 6480 / β ^ 2 := by sorry

end NNPartTree
