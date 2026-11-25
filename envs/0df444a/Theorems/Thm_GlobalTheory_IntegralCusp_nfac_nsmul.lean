-- Prove2me | Theorems.Thm_GlobalTheory_IntegralCusp_nfac_nsmul
-- name    : GlobalTheory.IntegralCusp.nfac_nsmul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:12:45.713021+00:00
-- url     : https://prove2.me/theorems/ba499af4-9671-5db1-a302-da314d9dff96
-- title:
--   Integral Cusp: nfac nsmul
-- statement:
--   The Integral Cusp construction uses the nfac nsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/BddOfMemHolSub.lean#L107-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/BddOfMemHolSub.lean#L107-L118

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_CuspStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_BddOfMemHolSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
noncomputable section
open GlobalTheory
open GlobalTheory.IntegralCusp
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.IntegralCusp.nfac_nsmul {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la la' : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r)
    (k : ℕ) (h : ∀ τ i, la' τ i = k * la τ i) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) :
    X.nfac la' x = X.nfac la x ^ k := by sorry
