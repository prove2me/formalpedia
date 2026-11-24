-- Prove2me | Theorems.Thm_GlobalTheory_JR_HermInv_charpoly_coeff_star
-- name    : GlobalTheory.JR.HermInv.charpoly_coeff_star
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:34:00.891889+00:00
-- url     : https://prove2.me/theorems/140aa0d8-719e-4541-b5c9-a042f3aaaccd
-- title:
--   Herm Inv: charpoly coeff star
-- statement:
--   The Herm Inv construction uses the charpoly coeff star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L158-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L158-L167

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

theorem GlobalTheory.JR.HermInv.charpoly_coeff_star (A : Matrix (Fin r) (Fin r) E) (hA : IsSelfAdjoint A) (i : ℕ) :
    star (A.charpoly.coeff i) = A.charpoly.coeff i := by sorry
