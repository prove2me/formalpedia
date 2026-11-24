-- Prove2me | Theorems.Thm_GlobalTheory_Published_LandherrSt_herm_eq
-- name    : GlobalTheory.Published.LandherrSt.herm_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:04:09.153395+00:00
-- url     : https://prove2.me/theorems/dee6999c-f610-4b9a-b311-b5e090d491b6
-- title:
--   Landherr St: herm eq
-- statement:
--   The Landherr St construction uses the herm eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Landherr₂/LandherrStIffLandherr.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Landherr₂/LandherrStIffLandherr.lean#L22-L25

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

theorem GlobalTheory.Published.LandherrSt.herm_eq (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y = x ⬝ᵥ (G *ᵥ fun b => _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (y b)) := by sorry
