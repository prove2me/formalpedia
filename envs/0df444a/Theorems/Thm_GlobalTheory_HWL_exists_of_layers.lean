-- Prove2me | Theorems.Thm_GlobalTheory_HWL_exists_of_layers
-- name    : GlobalTheory.HWL.exists_of_layers
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T02:52:33.786853+00:00
-- url     : https://prove2.me/theorems/67c2b311-e073-4ef5-9b32-67d9041e6668
-- title:
--   HWL: exists of layers
-- statement:
--   The HWL construction uses the exists of layers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsOfLayers.lean#L323-L331
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsOfLayers.lean#L323-L331

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsOfLayers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HWL
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct
variable {l : ℕ} [Fact l.Prime]
variable {P : LocPrime l} {K : FinExt l} {s : ℕ} {LL : FinExt l} {Γ : GamS P K s LL}
set_option maxHeartbeats 2000000

theorem GlobalTheory.HWL.exists_of_layers (P : LocPrime l) (AI : LocAinf l P)
    (h : ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → Nonempty (Layers P AI K s LL))
    (ht : ∀ K : FinExt l, P.ιB (AI.ιA AI.μ) - P.ιB P.tB ∈ (P.PD K).Fil 2)
    (hπ : ∀ K : FinExt l, ∃ u ∈ (P.PD K).Fil 0, P.ιB (AI.ιA AI.π₁) * u = 1) :
    ∃ H : LocHW l P, ∃ F : LocFon l P AI H, Nonempty (LocCmpT l P AI H F) := by sorry
