-- Prove2me | Theorems.Thm_GlobalTheory_JR_NormalFormL_companion_mulVec_ev
-- name    : GlobalTheory.JR.NormalFormL.companion_mulVec_ev
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:34:33.196324+00:00
-- url     : https://prove2.me/theorems/bc009ca6-98a7-457a-ab55-f20f0743a3d3
-- title:
--   Normal Form L: companion mul Vec ev
-- statement:
--   The Normal Form L construction uses the companion mul Vec ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisBorderedMatrixNormalFormInvariants.lean#L33-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisBorderedMatrixNormalFormInvariants.lean#L33-L39

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariants
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.NormalFormL
variable {k : Type} [Field k] {r : ℕ}

theorem GlobalTheory.JR.NormalFormL.companion_mulVec_ev (p : Fin r → k) (i : ℕ) (hi : i + 1 < r) :
    companion p *ᵥ ev r k i = ev r k (i + 1) := by sorry
