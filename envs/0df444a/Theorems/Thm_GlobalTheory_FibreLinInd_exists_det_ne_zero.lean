-- Prove2me | Theorems.Thm_GlobalTheory_FibreLinInd_exists_det_ne_zero
-- name    : GlobalTheory.FibreLinInd.exists_det_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:12:02.539424+00:00
-- url     : https://prove2.me/theorems/c7a23cfc-a062-48e3-8058-870ff5a736db
-- title:
--   Fibre Lin Ind: exists det ne zero
-- statement:
--   The Fibre Lin Ind construction uses the exists det ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsOpenSetOfLinearIndependentOnFibres.lean#L11-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsOpenSetOfLinearIndependentOnFibres.lean#L11-L39

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsOpenSetOfLinearIndependentOnFibres
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.FibreLinInd

theorem GlobalTheory.FibreLinInd.exists_det_ne_zero {K A : Type} [Field K] {r : ℕ} (v : A → Fin r → K)
    (h : ∀ c : Fin r → K, (∀ a, ∑ i, c i * v a i = 0) → c = 0) :
    ∃ a : Fin r → A, (Matrix.of fun k i => v (a k) i).det ≠ 0 := by sorry
