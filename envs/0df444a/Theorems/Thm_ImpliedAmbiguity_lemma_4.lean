-- Prove2me | Theorems.Thm_ImpliedAmbiguity_lemma_4
-- name    : ImpliedAmbiguity.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:05:46.245668+00:00
-- url     : https://prove2.me/theorems/b02c9b44-8f46-4b4b-94a4-6a7990ad432f
-- title:
--   Lemma 4 — the unique minimizer (33) and minimum (34) of $\theta\mapsto (v^\theta)^\top S v^\theta / x^\top\Sigma v^\theta$ on $(0,\bar\theta)$
-- statement:
--   Let $x, c\in\mathbb R^N$ and let $\Sigma, S$ be symmetric positive definite $N\times N$ matrices. For $\theta>0$ put $v^\theta = \theta^{-1}\Sigma^{-1}c - x$, and assume that $v^\theta \ne 0$ for every $\theta > 0$. Assume also $x\cdot c > 0$ and write $\bar\theta = (x^\top\Sigma x)^{-1}(x\cdot c)$. Consider
--
--   $$
--   f : (0,\bar\theta)\to\mathbb R_{++},\qquad f(\theta) = \frac{(v^\theta)^\top S v^\theta}{x^\top\Sigma v^\theta}. \tag{32}
--   $$
--
--   Let $\theta^*$ be given by
--
--   $$
--   \frac1{\theta^*} = \frac1{\bar\theta} + \left(\frac{(v^{\bar\theta})^\top S v^{\bar\theta}}{c^\top\Sigma^{-1}S\Sigma^{-1}c}\right)^{1/2}. \tag{33}
--   $$
--
--   Then
--
--   1. $f(\theta) > 0$ for every $\theta\in(0,\bar\theta)$;
--   2. $\theta^*\in(0,\bar\theta)$;
--   3. $f(\theta^*) \le f(\theta)$ for every $\theta\in(0,\bar\theta)$;
--   4. $\theta^*$ is the only minimizer of $f$ on $(0,\bar\theta)$;
--   5. the minimum value is
--   $$
--   f(\theta^*) = \frac{2}{x\cdot c}\left(\bigl(c^\top\Sigma^{-1}S\Sigma^{-1}c\bigr)^{1/2}\bigl((v^{\bar\theta})^\top S v^{\bar\theta}\bigr)^{1/2} + (v^{\bar\theta})^\top S\Sigma^{-1}c\right). \tag{34}
--   $$
--
--   With $S = \Sigma = \Sigma_R$ and $c = \mu - R_f\mathbf 1$, $f$ is the implied coefficient $\eta^\theta$ of (19), and Lemma 4 is the engine of Theorem 4.
--
--   Differences from the source:
--   - reading: "there is a unique θ > 0 that minimizes the function (0, θ̄) → R₊₊ … which is given by (33)" → the θ of (33) lies in (0, θ̄), minimizes f there, is its only minimizer there, and f > 0 on (0, θ̄); reason: the function's domain is (0, θ̄) and its stated codomain is R₊₊.
--   - encoding: θ̄ = (xᵀΣx)⁻¹(x·c), v^θ for θ > 0, (·)^{1/2}, S^N_++ → `thetaBar Sig c x` = (c ⬝ᵥ x)/(x ⬝ᵥ Σx) (the same number), `vTheta` total in θ, `Real.sqrt`, `Matrix.PosDef`, f total in θ and minimized over exactly `Set.Ioo 0 θ̄`; reason: Lean convention; same instances.
-- source:
--   Hara & Honda, Implied Ambiguity: Mean-Variance Efficiency and Pricing Errors, working paper (October 9, 2018; published version doi:10.1287/mnsc.2021.4097), Appendix C, Lemma 4, eqs. (32)–(34), p.41

import Mathlib
import Definitions.Def_ImpliedAmbiguity_thetaBar
import Definitions.Def_ImpliedAmbiguity_vTheta

open Matrix

namespace ImpliedAmbiguity

/-- Hara & Honda, *Implied Ambiguity: Mean-Variance Efficiency and Pricing Errors*, working
paper (October 9, 2018; published version Management Science 2022, doi:10.1287/mnsc.2021.4097),
Appendix C, Lemma 4, p.41: Let `x, c ∈ R^N`, `Σ, S ∈ S^N_++`. For `θ > 0` let
`v^θ = (1/θ)Σ⁻¹c − x` and assume there is no `θ > 0` with `v^θ = 0`. Assume `x · c > 0` and write
`θ̄ = (xᵀΣx)⁻¹(x · c)`. Then there is a unique `θ > 0` minimizing the function
(32) `(0, θ̄) → R_++, θ ↦ (v^θ)ᵀSv^θ / xᵀΣv^θ`, given by
(33) `1/θ = 1/θ̄ + ((v^θ̄)ᵀSv^θ̄ / cᵀΣ⁻¹SΣ⁻¹c)^{1/2}`, and the minimized value is
(34) `(2/x·c)((cᵀΣ⁻¹SΣ⁻¹c)^{1/2}((v^θ̄)ᵀSv^θ̄)^{1/2} + (v^θ̄)ᵀSΣ⁻¹c)`.

The conclusion states: (i) the function (32) is positive on `(0, θ̄)` (its codomain `R_++`);
(ii) the `θ` of (33) lies in `(0, θ̄)`; (iii) it minimizes (32) on `(0, θ̄)`; (iv) it is the only
minimizer there; (v) the minimum equals (34).

**Formalization Note.** `S^N_++` is `Matrix.PosDef`; `Σ` is named `Sig`. `x · c` is `x ⬝ᵥ c`;
`θ̄ = (xᵀΣx)⁻¹(x · c)` is `thetaBar Sig c x = (c ⬝ᵥ x)/(x ⬝ᵥ Sig *ᵥ x)`, the same number. `v^θ` is
`vTheta Sig c x θ` (total in `θ`). `(·)^{1/2}` is `Real.sqrt`; matrix inverses are Mathlib's. The
function (32) is written as a total function of `θ : ℝ` and minimized over exactly
`Set.Ioo 0 θ̄`. -/
theorem lemma_4 {N : ℕ} (x c : Fin N → ℝ) (Sig S : Matrix (Fin N) (Fin N) ℝ)
    (hSig : Sig.PosDef) (hS : S.PosDef)
    (hv : ∀ θ : ℝ, 0 < θ → vTheta Sig c x θ ≠ 0)
    (hxc : 0 < x ⬝ᵥ c) :
    let θbar := thetaBar Sig c x
    let f : ℝ → ℝ := fun θ =>
      (vTheta Sig c x θ ⬝ᵥ (S *ᵥ vTheta Sig c x θ)) / (x ⬝ᵥ (Sig *ᵥ vTheta Sig c x θ))
    let vbar := vTheta Sig c x θbar
    let A := c ⬝ᵥ ((Sig⁻¹ * S * Sig⁻¹) *ᵥ c)
    let θstar := (1 / θbar + Real.sqrt ((vbar ⬝ᵥ (S *ᵥ vbar)) / A))⁻¹
    (∀ θ ∈ Set.Ioo 0 θbar, 0 < f θ) ∧
    θstar ∈ Set.Ioo 0 θbar ∧
    IsMinOn f (Set.Ioo 0 θbar) θstar ∧
    (∀ θ ∈ Set.Ioo 0 θbar, f θ = f θstar → θ = θstar) ∧
    f θstar = 2 / (x ⬝ᵥ c) *
      (Real.sqrt A * Real.sqrt (vbar ⬝ᵥ (S *ᵥ vbar)) + vbar ⬝ᵥ ((S * Sig⁻¹) *ᵥ c)) := by sorry

end ImpliedAmbiguity
