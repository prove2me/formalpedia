-- Prove2me | Theorems.Thm_OptimalRLS_Upper_proposition_1_iv
-- name    : OptimalRLS.Upper.proposition_1_iv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T19:25:33.525597+00:00
-- url     : https://prove2.me/theorems/77bad1c2-6ca7-43f6-916c-405d89a4c332
-- title:
--   Proposition 1 iv), (25), p. 12 — for λ > 0 the regularized expected risk has a unique minimizer, (T + λ)f^λ = T f_H
-- statement:
--   Assume Hypotheses 1 and 2 with a minimizer $f_{\mathcal H}$ of the expected risk. For every $\lambda>0$ the regularized expected risk
--   $$\mathcal E[f]+\lambda\|f\|_{\mathcal H}^2$$
--   has a unique minimizer $f^\lambda\in\mathcal H$, and it satisfies
--   $$f^\lambda=(T+\lambda)^{-1}Tf_{\mathcal H},\qquad\text{i.e.}\qquad\langle Tf^\lambda,h\rangle_{\mathcal H}+\lambda\langle f^\lambda,h\rangle_{\mathcal H}=\langle Tf_{\mathcal H},h\rangle_{\mathcal H}\quad\text{for all }h\in\mathcal H.$$
--
--   The population minimizer $f^\lambda$ is the reference point of the bias–variance split in Theorem 4: the residual $\mathcal A(\lambda)$ and the reconstruction error $\mathcal B(\lambda)$ are measured at $f^\lambda$.
--
--   **Formalization Note** $\langle Tf,h\rangle_{\mathcal H}$ is `covForm ρ.fst f h`. The paper's (25) also writes $f^\lambda=(T+\lambda)^{-1}g$ with $g=Tf_{\mathcal H}$ by (22); the statement records the normal equation, which is equivalent to (25) because $T+\lambda$ is invertible.
-- source:
--   Caponnetto & De Vito, Found. Comput. Math. 7 (2007), authors' copy, Proposition 1 iv), (25), p. 12

import Mathlib
import Definitions.Def_OptimalRLS_Upper_Setting

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace OptimalRLS.Upper

/-- **Proposition 1 iv), (25)** (p. 12). Under Hypotheses 1 and 2, for every `λ > 0` the
regularized expected risk `E[f] + λ‖f‖²_H` has a unique minimizer `f^λ`, and it satisfies
`(T + λ) f^λ = T f_H`, i.e. `⟨T f^λ, h⟩_H + λ⟨f^λ, h⟩_H = ⟨T f_H, h⟩_H` for every `h ∈ H`
(the quadratic form of `T` is `covForm ρ.fst`). -/
theorem proposition_1_iv
    {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    [TopologicalSpace.SeparableSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H] [RKHS ℝ H X Y]
    {ι : Type*} (κ : ℝ) (v : HilbertBasis ι ℝ Y) (h1 : Hyp1 X H κ v)
    (M Sig : ℝ) (ρ : Measure (X × Y)) [IsProbabilityMeasure ρ] (fH : H)
    (h2 : Hyp2 M Sig ρ fH) (lam : ℝ) (hlam : 0 < lam) :
    (∃! fl : H, ∀ f : H, regRisk ρ lam fl ≤ regRisk ρ lam f) ∧
      ∀ fl : H, (∀ f : H, regRisk ρ lam fl ≤ regRisk ρ lam f) →
        ∀ h : H, covForm ρ.fst fl h + lam * ⟪fl, h⟫_ℝ = covForm ρ.fst fH h := by sorry

end OptimalRLS.Upper
