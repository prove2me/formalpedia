-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_local_coefficients_surjective
-- name    : OAI.PiExponent.LogarithmicJetIdeals.formalJet_local_coefficients_surjective
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-15T05:00:33.627514+00:00
-- url     : https://prove2.me/theorems/9352af23-4740-4a57-9d63-a78552e87cbe
-- title:
--   Surjectivity of finite formal logarithmic jet coefficients at one center
-- statement:
--   At each fixed center, a polynomial can realize any prescribed finite set of formal logarithmic jet coefficients, provided the requested slot-degree pairs are distinct.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.formalJet_local_coefficients_surjective
    {ι α : Type} [Fintype α] [DecidableEq α] {m : ℕ}
    (center : ι → Fin m → ℂ) (slot : α → ι)
    (degree : α → Fin (m + 1) → ℕ)
    (hindex : Function.Injective (fun a : α => (slot a, degree a)))
    (value : α → ℂ) :
    ∀ i : ι, ∃ Q : MvPolynomial (Fin (m + 1)) ℂ,
      ∀ b : α, slot b = i →
        MvPowerSeries.coeff
          (Finsupp.equivFunOnFinite.symm (degree b))
          (formalJet (center i) Q) = value b := by sorry
