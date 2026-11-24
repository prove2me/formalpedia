-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DSCoreSub_ofFn_prod_intertwine
-- name    : GlobalTheory.CompanionTheory.DSCoreSub.ofFn_prod_intertwine
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:34:29.644188+00:00
-- url     : https://prove2.me/theorems/5647e114-d031-4841-8ef5-7b5ae9e45ca5
-- title:
--   DSCore Sub: of Fn prod intertwine
-- statement:
--   The DSCore Sub construction uses the of Fn prod intertwine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AlgCoreSubOfAlgCore.lean#L13-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AlgCoreSubOfAlgCore.lean#L13-L19

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

theorem GlobalTheory.CompanionTheory.DSCoreSub.ofFn_prod_intertwine (φ : V' →ₗ[ℂ] V) :
    ∀ {t : ℕ} (f' : Fin t → Module.End ℂ V') (f : Fin t → Module.End ℂ V),
      (∀ k x, φ (f' k x) = f k (φ x)) → ∀ x, φ ((List.ofFn f').prod x) = (List.ofFn f).prod (φ x)
  := by sorry
