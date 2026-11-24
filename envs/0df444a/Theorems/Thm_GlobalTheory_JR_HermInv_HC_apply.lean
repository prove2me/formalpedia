-- Prove2me | Theorems.Thm_GlobalTheory_JR_HermInv_HC_apply
-- name    : GlobalTheory.JR.HermInv.HC_apply
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:36:15.65309+00:00
-- url     : https://prove2.me/theorems/d346aef0-8ade-42fa-a9e2-f656e02ba403
-- title:
--   Herm Inv: HC apply
-- statement:
--   The Herm Inv construction uses the HC apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L387-L397
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L387-L397

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

theorem GlobalTheory.JR.HermInv.HC_apply {K : Type} [CommRing K] (a : Inv r K) (i j : Fin r) :
    (hankel a * companion a.1) i j = mom (sec a) ((i : ℕ) + j + 1) := by sorry
