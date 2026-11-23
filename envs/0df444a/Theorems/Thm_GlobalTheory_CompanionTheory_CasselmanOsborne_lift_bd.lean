-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CasselmanOsborne_lift_bd
-- name    : GlobalTheory.CompanionTheory.CasselmanOsborne.lift_bd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:29.64054+00:00
-- url     : https://prove2.me/theorems/a8270f80-b54c-42e8-9df9-36ca4c2864fc
-- title:
--   Casselman Osborne: lift bd
-- statement:
--   The Casselman Osborne construction uses the lift bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ZetaDegZero.lean#L113-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ZetaDegZero.lean#L113-L119

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ZetaDegZero
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CasselmanOsborne
open Formalism.REAL (GlRel qdet qminor Tm)
open CompanionTheory.D.DSIC
variable {n : ℕ} {ε : Fin n → Bool} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem GlobalTheory.CompanionTheory.CasselmanOsborne.lift_bd (φ : V →ₗ[ℂ] W) (E : Fin n → Fin n → Module.End ℂ V) (F : Fin n → Fin n → Module.End ℂ W)
    (h : ∀ a b x, φ (E a b x) = F a b (φ x)) (x : Ch ε V) : lift ε φ (bd ε E x) = bd ε F (lift ε φ x) := by sorry
