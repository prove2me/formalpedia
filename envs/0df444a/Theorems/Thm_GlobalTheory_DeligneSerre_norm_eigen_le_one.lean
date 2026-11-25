-- Prove2me | Theorems.Thm_GlobalTheory_DeligneSerre_norm_eigen_le_one
-- name    : GlobalTheory.DeligneSerre.norm_eigen_le_one
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:08:18.266697+00:00
-- url     : https://prove2.me/theorems/402ae87c-d862-5e05-bd16-5ec1cfbe1207
-- title:
--   Deligne Serre: norm eigen le one
-- statement:
--   The Deligne Serre construction uses the norm eigen le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIntegralHeckeEigensystemDeligneSerre.lean#L68-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIntegralHeckeEigensystemDeligneSerre.lean#L68-L78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixExistsCommonEigenvectorMemStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteJointEigensystemsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMatricesIntertwiningOfSemilinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormEigenvalueLeOneOfEntries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIntegralHeckeEigensystemDeligneSerre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.DeligneSerre

theorem GlobalTheory.DeligneSerre.norm_eigen_le_one (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] (emb : O →+* PadicAlgCl l)
    (hle : ∀ a, ‖emb a‖ ≤ 1) (n : ℕ) (N : Matrix (Fin n) (Fin n) O) (c : Fin n → PadicAlgCl l)
    (μ : PadicAlgCl l) (hc : c ≠ 0) (hN : N.map emb *ᵥ c = μ • c) : ‖μ‖ ≤ 1 := by sorry
