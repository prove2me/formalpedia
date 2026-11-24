-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HatBound_exists_nsmul_mem_lattice
-- name    : GlobalTheory.CompanionTheory.HatBound.exists_nsmul_mem_lattice
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:23:33.256803+00:00
-- url     : https://prove2.me/theorems/85481223-47a6-4a0b-8794-9c91708be99a
-- title:
--   Hat Bound: exists nsmul mem lattice
-- statement:
--   The Hat Bound construction uses the exists nsmul mem lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/NefEffectiveCones/ExistsNsmulMulVecMemHat.lean#L33-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/NefEffectiveCones/ExistsNsmulMulVecMemHat.lean#L33-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_SupportedAtSplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_NefEffectiveCones_ExistsNsmulMulVecMemHat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HatBound
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem GlobalTheory.CompanionTheory.HatBound.exists_nsmul_mem_lattice [NumberField E] (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ m : ℕ, 0 < m ∧ m • x ∈ L := by sorry
