-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSVerma_inner_sum
-- name    : GlobalTheory.CompanionTheory.DSVerma.inner_sum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:49.990193+00:00
-- url     : https://prove2.me/theorems/f7e639d8-8de2-4c0d-8b9e-acea53a79478
-- title:
--   DSVerma: inner sum
-- statement:
--   The DSVerma construction uses the inner sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/KummerLiftedCocycleImageEqPicardClass.lean#L35-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/KummerLiftedCocycleImageEqPicardClass.lean#L35-L55

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_KummerLiftedCocycleImageEqPicardClass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSVerma
open CompanionTheory.D.DSIC Formalism.REAL
variable {n : ℕ} {ε : Fin n → Bool}
variable {R : Type} [Ring R] (Y : NC ε → R) (u v : Fin n → Fin n → R)

theorem GlobalTheory.CompanionTheory.DSVerma.inner_sum
    (huY : ∀ a c j, u a c * Y j - Y j * u a c = -(if a = j.1.1 ∧ c = j.1.2 then 1 else 0))
    (hvY : ∀ a c j, v a c * Y j - Y j * v a c = if a = j.1.1 ∧ c = j.1.2 then 1 else 0)
    (i : NC ε) (c d e f : Fin n) :
    (∑ j : NC ε, ((u i.1.1 c * v d i.1.2) * Y j - Y j * (u i.1.1 c * v d i.1.2)) * (u j.1.1 e * v f j.1.2)) =
      u i.1.1 c * (if ε d = true then u d e else 0) * v f i.1.2 -
        v d i.1.2 * u i.1.1 e * (if ε c = false then v f c else 0) := by sorry
