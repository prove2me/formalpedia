-- Prove2me | Theorems.Thm_GlobalTheory_JR_HermInv_pow_r_of
-- name    : GlobalTheory.JR.HermInv.pow_r_of
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:33:30.497063+00:00
-- url     : https://prove2.me/theorems/cf42492b-bd73-4369-bf7a-66b57bdefcfe
-- title:
--   Herm Inv: pow r of
-- statement:
--   The Herm Inv construction uses the pow r of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L307-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L307-L311

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

theorem GlobalTheory.JR.HermInv.pow_r_of (X : Hn r F E) (a : Inv r F) (h : HasInv X a) :
    X.1.1 ^ r *ᵥ X.2.1 = -(Bm X.toGl *ᵥ fun i => algebraMap F E (a.1 i)) := by sorry
