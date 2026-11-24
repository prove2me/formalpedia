-- Prove2me | Theorems.Thm_GlobalTheory_JR_HermInv_charpoly_actU
-- name    : GlobalTheory.JR.HermInv.charpoly_actU
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:33:39.638258+00:00
-- url     : https://prove2.me/theorems/e1d2f53a-dcc6-4415-975e-af3c2ba2b707
-- title:
--   Herm Inv: charpoly act U
-- statement:
--   The Herm Inv construction uses the charpoly act U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L210-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L210-L213

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

theorem GlobalTheory.JR.HermInv.charpoly_actU (g : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) :
    (actU g X).1.1.charpoly = X.1.1.charpoly := by sorry
