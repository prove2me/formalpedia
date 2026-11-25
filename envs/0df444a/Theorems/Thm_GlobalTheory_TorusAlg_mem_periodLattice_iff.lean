-- Prove2me | Theorems.Thm_GlobalTheory_TorusAlg_mem_periodLattice_iff
-- name    : GlobalTheory.TorusAlg.mem_periodLattice_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T17:18:29.617566+00:00
-- url     : https://prove2.me/theorems/08fdaa2d-16a3-549a-bad9-0d5d714bd768
-- title:
--   Torus Alg: mem period Lattice iff
-- statement:
--   The Torus Alg construction uses the mem period Lattice iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Statements/ThetaLevelCharacters/MemThetaLevelCharDimZero.lean#L64-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Statements/ThetaLevelCharacters/MemThetaLevelCharDimZero.lean#L64-L66

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Statements_ThetaLevelCharacters_MemThetaLevelCharDimZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.TorusAlg
open ReciprocityTheory.PTheta
variable {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℂ}

theorem GlobalTheory.TorusAlg.mem_periodLattice_iff (z : Fin g → ℂ) : z ∈ periodLattice τ ↔
    ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)) := by sorry
