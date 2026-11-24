-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KModExists_kHighest_iff
-- name    : GlobalTheory.CompanionTheory.KModExists.kHighest_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:49:25.081411+00:00
-- url     : https://prove2.me/theorems/301f4744-0fd7-4650-bb10-87396b66ab72
-- title:
--   KMod Exists: k Highest iff
-- statement:
--   The KMod Exists construction uses the k Highest iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CompactFiniteAdelesAwayPBoundedDenominators.lean#L14-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CompactFiniteAdelesAwayPBoundedDenominators.lean#L14-L26

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CompactFiniteAdelesAwayPBoundedDenominators
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KModExists
open Formalism.REAL (GlRel IsUnitary KHighest IsWeight)
open PI.UpqRep (IsKFin IsKTypeOf IsKStableOn)
open CompanionTheory.D.DSIC

theorem GlobalTheory.CompanionTheory.KModExists.kHighest_iff {n : ℕ} (ε : Fin n → Bool) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (ι : V →ₗ[ℂ] W) (hι : Function.Injective ι) (E' : Fin n → Fin n → Module.End ℂ V)
    (E : Fin n → Fin n → Module.End ℂ W) (h : ∀ a b v, ι (E' a b v) = E a b (ι v)) (μ : Fin n → ℝ) (v : V) :
    KHighest ε E' μ v ↔ KHighest ε E μ (ι v) := by sorry
