-- Prove2me | Theorems.Thm_GlobalTheory_PowSec_exists_indep_sections
-- name    : GlobalTheory.PowSec.exists_indep_sections
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:57:03.469678+00:00
-- url     : https://prove2.me/theorems/fd1def28-e6f5-450a-8b2f-85fedecdfacb
-- title:
--   Pow Sec: exists indep sections
-- statement:
--   The Pow Sec construction uses the exists indep sections property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsIndepSections.lean#L73-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsIndepSections.lean#L73-L104

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIndepSections
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.PowSec
attribute [local instance] Over.cartesianMonoidalCategory
open Out

theorem GlobalTheory.PowSec.exists_indep_sections (H : Out.GlobalSectionsRankAlgClosed) (P : Out.PolAV (Sp ℂ)) (n : ℕ) (hn : 1 ≤ n) :
    ∃ s : Fin (n ^ P.g) → (lbPow P.L n).Sec, ∀ a : Fin (n ^ P.g) → ℂ,
      (∀ j, ∑ i, constFn P.A.hom _ (a i) * (s i).f j = 0) → a = 0 := by sorry
