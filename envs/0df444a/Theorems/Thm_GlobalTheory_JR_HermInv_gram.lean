-- Prove2me | Theorems.Thm_GlobalTheory_JR_HermInv_gram
-- name    : GlobalTheory.JR.HermInv.gram
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:05.004154+00:00
-- url     : https://prove2.me/theorems/3ea7e562-2c2f-406e-99d0-1c8fb00c04c1
-- title:
--   Herm Inv: gram
-- statement:
--   The Herm Inv construction uses the gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L280-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L280-L286

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

theorem GlobalTheory.JR.HermInv.gram (X : Hn r F E) : (Bm X.toGl)ᴴ * Bm X.toGl = Matrix.of fun i j : Fin r => mom X.toGl ((i : ℕ) + j) := by sorry
