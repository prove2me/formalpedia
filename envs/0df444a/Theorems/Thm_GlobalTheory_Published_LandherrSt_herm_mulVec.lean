-- Prove2me | Theorems.Thm_GlobalTheory_Published_LandherrSt_herm_mulVec
-- name    : GlobalTheory.Published.LandherrSt.herm_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:43:03.887614+00:00
-- url     : https://prove2.me/theorems/5ab24e23-e61e-4674-8cdb-a6aafceb084e
-- title:
--   Landherr St: herm mul Vec
-- statement:
--   The Landherr St construction uses the herm mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Landherr₂/LandherrStIffLandherr.lean#L31-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Landherr₂/LandherrStIffLandherr.lean#L31-L38

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__LandherrStIffLandherr_9fec213082f17e18
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.LandherrSt
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
open NumberField Matrix
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.Published.LandherrSt.herm_mulVec (G P : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G (P *ᵥ x) (P *ᵥ y) = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm (Pᵀ * G * P.map _root_.ReciprocityTheory.ChartRestriction.G.FD.cc) x y := by sorry
