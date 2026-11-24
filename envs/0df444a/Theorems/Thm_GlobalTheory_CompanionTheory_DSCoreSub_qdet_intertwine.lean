-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSCoreSub_qdet_intertwine
-- name    : GlobalTheory.CompanionTheory.DSCoreSub.qdet_intertwine
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:34:34.720467+00:00
-- url     : https://prove2.me/theorems/cfb4ca6f-cf52-4a66-9ffc-379d833a294b
-- title:
--   DSCore Sub: qdet intertwine
-- statement:
--   The DSCore Sub construction uses the qdet intertwine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AlgCoreSubOfAlgCore.lean#L21-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AlgCoreSubOfAlgCore.lean#L21-L30

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AlgCoreSubOfAlgCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL CompanionTheory.D.DSIC
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSCoreSub
variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {n : ℕ}

theorem GlobalTheory.CompanionTheory.DSCoreSub.qdet_intertwine (φ : V' →ₗ[ℂ] V) (E' : Fin n → Fin n → Module.End ℂ V')
    (E : Fin n → Fin n → Module.End ℂ V) (h : ∀ a b x, φ (E' a b x) = E a b (φ x)) (u : ℂ) (x : V') :
    φ (qdet E' u x) = qdet E u (φ x) := by sorry
