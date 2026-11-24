-- Prove2me | Theorems.Thm_GlobalTheory_JR_HermInv_sec_rec
-- name    : GlobalTheory.JR.HermInv.sec_rec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:56.718796+00:00
-- url     : https://prove2.me/theorems/2ec6744f-5bee-4f16-abe1-3375114a8a72
-- title:
--   Herm Inv: sec rec
-- statement:
--   The Herm Inv construction uses the sec rec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L134-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L134-L136

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
variable {r : ℕ} {K : Type} [CommRing K]

theorem GlobalTheory.JR.HermInv.sec_rec (a : Inv r K) (k : ℕ) :
    mom (sec a) (k + r) = -((fun j : Fin r => mom (sec a) (k + j)) ⬝ᵥ a.1) := by sorry
