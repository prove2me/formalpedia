-- Prove2me | Theorems.Thm_GlobalTheory_JR_HermInv_mom_actU
-- name    : GlobalTheory.JR.HermInv.mom_actU
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:33:12.867672+00:00
-- url     : https://prove2.me/theorems/ff826d16-752b-4737-bbf5-77a5e18b6d76
-- title:
--   Herm Inv: mom act U
-- statement:
--   The Herm Inv construction uses the mom act U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L215-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L215-L219

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

theorem GlobalTheory.JR.HermInv.mom_actU (g : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) (k : ℕ) :
    mom (actU g X).toGl k = mom X.toGl k := by sorry
