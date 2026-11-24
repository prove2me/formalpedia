-- Prove2me | Theorems.Thm_GlobalTheory_JR_HermInv_mulVec_ev
-- name    : GlobalTheory.JR.HermInv.mulVec_ev
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:33:33.409261+00:00
-- url     : https://prove2.me/theorems/8f2c862c-7ad3-4cd5-97ab-7d7fe434fae0
-- title:
--   Herm Inv: mul Vec ev
-- statement:
--   The Herm Inv construction uses the mul Vec ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L415-L422
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L415-L422

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.HermInv
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
variable {r : ℕ}

theorem GlobalTheory.JR.HermInv.mulVec_ev {K : Type} [CommRing K] (M : Matrix (Fin r) (Fin r) K) (j : Fin r) :
    M *ᵥ ev r K j = fun i => M i j := by sorry
