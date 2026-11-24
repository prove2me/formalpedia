-- Prove2me | Theorems.Thm_GlobalTheory_FockAdj_map_rowAct
-- name    : GlobalTheory.FockAdj.map_rowAct
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:34:21.486318+00:00
-- url     : https://prove2.me/theorems/958588df-3507-4bb3-9a8f-2f712fdaf0bb
-- title:
--   Fock Adj: map row Act
-- statement:
--   The Fock Adj construction uses the map row Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FockQWordRowActAdj.lean#L20-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FockQWordRowActAdj.lean#L20-L30

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FockQWordRowActAdj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
open GlobalTheory GlobalTheory.FockAdj

theorem GlobalTheory.FockAdj.map_rowAct {r n : ℕ} (g : Matrix (Fin r) (Fin r) ℚ) (f : MvPolynomial (Fin r × Fin n) ℚ) :
    map (Rat.castHom ℂ) (rowAct ℚ g f) =
      rowAct ℂ (g.map (Rat.castHom ℂ)) (map (Rat.castHom ℂ) f) := by sorry
