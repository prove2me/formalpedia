-- Prove2me | Theorems.Thm_GlobalTheory_JR_HermInv_mom_sec_lt
-- name    : GlobalTheory.JR.HermInv.mom_sec_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:06.926861+00:00
-- url     : https://prove2.me/theorems/7c72153b-0cf0-4e7d-9769-4a1d9cd94341
-- title:
--   Herm Inv: mom sec lt
-- statement:
--   The Herm Inv construction uses the mom sec lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L138-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L138-L145

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

theorem GlobalTheory.JR.HermInv.mom_sec_lt (a : Inv r K) (i : Fin r) : mom (sec a) i = a.2.1 i := by sorry
