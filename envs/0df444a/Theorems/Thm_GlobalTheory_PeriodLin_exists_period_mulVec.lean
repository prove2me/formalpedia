-- Prove2me | Theorems.Thm_GlobalTheory_PeriodLin_exists_period_mulVec
-- name    : GlobalTheory.PeriodLin.exists_period_mulVec
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:20:37.818591+00:00
-- url     : https://prove2.me/theorems/14b8b271-5128-4b16-b2e3-7303df2ae989
-- title:
--   Period Lin: exists period mul Vec
-- statement:
--   The Period Lin construction uses the exists period mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsPeriodMulVec.lean#L21-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsPeriodMulVec.lean#L21-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsPreconnectedBlockUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsPeriodMulVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.PeriodLin
open NumberField AlgebraicGeometry CategoryTheory Limits
open scoped Matrix nonZeroDivisors

theorem GlobalTheory.PeriodLin.exists_period_mulVec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (h₀ : Matrix (Fin g) (Fin g) ℂ), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty P → IsUnit h₀.det → (∀ j j', h₀ j j' ≠ 0 → ty j = ty j') → ∃ P' : D.La →+ (Fin g → ℂ), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty P' ∧ ∀ a, P' a = h₀ *ᵥ P a := by sorry
