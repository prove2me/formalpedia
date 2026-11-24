-- Prove2me | Theorems.Thm_GlobalTheory_CuspBasis_pair_change
-- name    : GlobalTheory.CuspBasis.pair_change
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:51:03.522519+00:00
-- url     : https://prove2.me/theorems/504d7cbf-b4ff-4435-ac16-0a49c1b0285e
-- title:
--   Cusp Basis: pair change
-- statement:
--   The Cusp Basis construction uses the pair change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExponentMatchingIndependentOfCuspBasis.lean#L103-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExponentMatchingIndependentOfCuspBasis.lean#L103-L106

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ZMatEInjective
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SpanRatSmulMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExponentMatchingIndependentOfCuspBasis
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
open GlobalTheory GlobalTheory.CuspBasis
open GlobalTheory.CuspCentre
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
variable {X : Data E r} {cu₀ cu : FJ.CuspFD X ρ} {P : Matrix (Fin ρ) (Fin ρ) E}

theorem GlobalTheory.CuspBasis.pair_change (P : Matrix (Fin ρ) (Fin ρ) E) (l x : Fin ρ → E) :
    ∑ i, (P *ᵥ l) i * x i = ∑ i, l i * (x ᵥ* P) i := by sorry
