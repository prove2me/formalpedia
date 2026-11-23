-- Prove2me | Theorems.Thm_GlobalTheory_LatticeHom_re_hermForm_real_smul
-- name    : GlobalTheory.LatticeHom.re_hermForm_real_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:34:53.189458+00:00
-- url     : https://prove2.me/theorems/53202043-62fb-4528-aede-1cc5d95175c9
-- title:
--   Lattice Hom: re herm Form real smul
-- statement:
--   The Lattice Hom construction uses the re herm Form real smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/HermFormSwapOfIsHermitian.lean#L67-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/HermFormSwapOfIsHermitian.lean#L67-L72

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_SectionsPowThetaFunctions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_HermFormSwapOfIsHermitian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LatticeHom

theorem GlobalTheory.LatticeHom.re_hermForm_real_smul {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (t : ℝ) (z : Fin g → ℂ) :
    (hermForm Hm (t • z) (t • z)).re = t ^ 2 * (hermForm Hm z z).re := by sorry
