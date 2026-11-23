-- Prove2me | Theorems.Thm_GlobalTheory_JR_HermInv_gram_hankel
-- name    : GlobalTheory.JR.HermInv.gram_hankel
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:04.341738+00:00
-- url     : https://prove2.me/theorems/1751502d-b317-4a9e-8a57-4dd871e85ae0
-- title:
--   Herm Inv: gram hankel
-- statement:
--   The Herm Inv construction uses the gram hankel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L288-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L288-L292

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

theorem GlobalTheory.JR.HermInv.gram_hankel (X : Hn r F E) (a : Inv r F) (h : HasInv X a) :
    (Bm X.toGl)ᴴ * Bm X.toGl = (hankel a).map (algebraMap F E) := by sorry
