-- Prove2me | Theorems.Thm_GlobalTheory_HolPeriods_exists_local_section
-- name    : GlobalTheory.HolPeriods.exists_local_section
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:38:22.270106+00:00
-- url     : https://prove2.me/theorems/93743c67-9e09-415f-b4ba-324f0e7856b5
-- title:
--   Hol Periods: exists local section
-- statement:
--   The Hol Periods construction uses the exists local section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsDifferentiableOnTransfer.lean#L51-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsDifferentiableOnTransfer.lean#L51-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDifferentiableOnTransfer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HolPeriods

theorem GlobalTheory.HolPeriods.exists_local_section {n : ℕ} {U : Set (Fin n → ℂ)} {F : (Fin n → ℂ) → (Fin n → ℂ)} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {a : Fin n → ℂ} (ha : a ∈ U) (hb : Function.Bijective (fderiv ℂ F a)) :
    ∃ (W : Set (Fin n → ℂ)) (G : (Fin n → ℂ) → (Fin n → ℂ)), IsOpen W ∧ F a ∈ W ∧ DifferentiableOn ℂ G W ∧
      ∀ w ∈ W, G w ∈ U ∧ F (G w) = w := by sorry
