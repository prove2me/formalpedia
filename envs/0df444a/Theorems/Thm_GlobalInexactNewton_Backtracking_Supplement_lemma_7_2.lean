-- Prove2me | Theorems.Thm_GlobalInexactNewton_Backtracking_Supplement_lemma_7_2
-- name    : GlobalInexactNewton.Backtracking.Supplement.lemma_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T08:54:09.605852+00:00
-- url     : https://prove2.me/theorems/69e28a6c-286b-4d0f-9173-30e52b76ac5d
-- title:
--   Lemma 7.2 — Equality curve angle controls the step with the exact factor 2‖F′(x_k)⁻¹‖/γ_k near η = 1.
-- statement:
--   Let $\sigma$ be a continuous equality curve at $x$ on $[\bar\eta,1]$, with $\bar\eta\in[0,1)$ and $\sigma(1)=0$. Assume $F(x)\ne0$, $F'(x)$ invertible, and $\gamma_x=\inf_{\bar\eta\le\eta<1}|\langle F(x),F'(x)\sigma(\eta)\rangle|/(\|F(x)\|\|F'(x)\sigma(\eta)\|)>0$. Then
--
--   $$\|\sigma(\eta)\|\le\frac{2\|F'(x)^{-1}\|}{\gamma_x}(1-\eta)\|F(x)\|\quad\text{for }\max\{\bar\eta,\sqrt{1-\gamma_x^2}\}\le\eta\le1.$$
--
--   The exact coefficient and both endpoints are retained. This provides the local step bound used in Theorem 7.3.
--
--   **Formalization Note** The paper states the estimate at an algorithm iteration; we state its local equality-curve version. The paper states its results on $\mathbb R^n$; we use a finite-dimensional real space with exactly its specified norm and `ContDiff ℝ 1 F`. All curve restrictions refer only to their stated level intervals.
--
--   Differences from the source:
--   - encoding: Real n-dimensional vectors, continuously differentiable F, and the paper’s algorithm or local data. → Finite-dimensional real normed spaces (inner product spaces in §§7–8), fderiv with ContDiff ℝ 1, and explicit data predicates.; reason: These are coordinate-independent representations with exactly the stated norm; a run on infinite sequences means no breakdown.
--   - generalization: Lemma 7.2 is stated at an iteration of ECMR or ECTL. → The same estimate holds for any local continuous equality curve with initial level in [0,1).; reason: Only the equality, continuity and zero endpoint are used in pp. 413–414; trial acceptance and previous iterations play no role, so no source case is excluded.
-- source:
--   Eisenstat and Walker, Globally Convergent Inexact Newton Methods, SIAM J. Optim. 4(2) (1994), p. 413, Lemma 7.2; DOI 10.1137/0804022

import Mathlib
import Definitions.Def_GlobalInexactNewton_Backtracking_Method
import Definitions.Def_GlobalInexactNewton_Backtracking_Supplement_EqualityCurves

namespace GlobalInexactNewton.Backtracking.Supplement

open Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem lemma_7_2 (F : E → E) (hF : ContDiff ℝ 1 F) (x : E)
    (ηbar : ℝ) (σ : ℝ → E) (hlevel : ηbar ∈ Set.Ico (0 : ℝ) 1)
    (hcurve : IsEqualityCurve F x ηbar σ) (hFx : F x ≠ 0)
    (hγ : 0 < curveAngle F x ηbar σ) (hinv : (fderiv ℝ F x).IsInvertible) :
    ∀ η ∈ Set.Icc (max ηbar (Real.sqrt (1 - (curveAngle F x ηbar σ) ^ 2))) 1,
      ‖σ η‖ ≤ (2 * ‖(fderiv ℝ F x).inverse‖ / curveAngle F x ηbar σ) *
        (1 - η) * ‖F x‖ := by sorry

end GlobalInexactNewton.Backtracking.Supplement
