-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_Model_coc_twist
-- name    : GlobalTheory.Cyc.Model.coc_twist
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:03:16.255896+00:00
-- url     : https://prove2.me/theorems/25c1a3b4-d216-5562-8069-d92810f93433
-- title:
--   Model: coc twist
-- statement:
--   The Model construction uses the coc twist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/PowLtFirstRadius.lean#L284-L306
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/PowLtFirstRadius.lean#L284-L306

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_PowLtFirstRadius
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.Model
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
variable {l : ℕ} [Fact l.Prime]

theorem GlobalTheory.Cyc.Model.coc_twist (G : Subgroup (GQ l)) :
    CobOn G (twAct actC chi 1 (fun _ => (1 : Matrix (Fin 1) (Fin 1) (PadicComplex l)))) (ball l 1)
      (fun σ _ => chiC chi 1 σ - 1) ∧
    CocOn G (twAct actC chi 1 (fun _ => (1 : Matrix (Fin 1) (Fin 1) (PadicComplex l)))) (ball l 1)
      (fun σ _ => chiC chi 1 σ - 1) := by sorry
