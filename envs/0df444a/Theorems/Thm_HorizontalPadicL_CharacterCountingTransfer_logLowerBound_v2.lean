-- Prove2me | Theorems.Thm_HorizontalPadicL_CharacterCountingTransfer_logLowerBound_v2
-- name    : HorizontalPadicL.CharacterCountingTransfer.logLowerBound_v2
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-25T14:07:32.976041+00:00
-- url     : https://prove2.me/theorems/e87b39ac-8504-4928-92a3-6c1d6bfdd35b
-- title:
--   Bounded-multiplicity maps preserve logarithmic lower bounds
-- statement:
--   A map with uniformly bounded finite fibres and bounded conductor growth
--   preserves logarithmic-power lower bounds. Explicit finiteness assumptions
--   prevent Set.ncard of an infinite set from silently becoming zero.
-- source:
--   Kriz--Nordentoft, Horizontal p-adic L-functions, https://arxiv.org/pdf/2310.20678, Section 2.3.3, Lemma 5.7, Theorem 5.9 and Corollary 5.10.

import Definitions.Def_KN_PrimePowerPropagationV2

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace HorizontalPadicL

/-- A map with uniformly bounded finite fibres and bounded conductor growth
preserves logarithmic-power lower bounds. Explicit finiteness assumptions
prevent Set.ncard of an infinite set from silently becoming zero. -/
theorem CharacterCountingTransfer.logLowerBound_v2
    {S T : Set DirichletCharacterWithLevel}
    (F : CharacterCountingTransfer S T)
    (hS : ∀ X : ℝ, {χ | χ ∈ S ∧ (χ.2.conductor : ℝ) ≤ X}.Finite)
    (hT : ∀ X : ℝ, {χ | χ ∈ T ∧ (χ.2.conductor : ℝ) ≤ X}.Finite)
    (α : ℝ) (hα : 0 < α)
    (hcount : HasLogPowerLowerBound (characterConductorCount S) α) :
    HasLogPowerLowerBound (characterConductorCount T) α := by
  sorry

end HorizontalPadicL
