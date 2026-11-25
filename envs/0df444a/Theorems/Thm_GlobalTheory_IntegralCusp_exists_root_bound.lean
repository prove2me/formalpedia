-- Prove2me | Theorems.Thm_GlobalTheory_IntegralCusp_exists_root_bound
-- name    : GlobalTheory.IntegralCusp.exists_root_bound
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:12:52.582734+00:00
-- url     : https://prove2.me/theorems/0d7fb410-4d3e-550f-9ff1-f2262cdbe7ea
-- title:
--   Integral Cusp: exists root bound
-- statement:
--   The Integral Cusp construction uses the exists root bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/BddOfMemHolSub.lean#L40-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/BddOfMemHolSub.lean#L40-L100

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain

theorem GlobalTheory.IntegralCusp.exists_root_bound (N k m : ℕ) (cf : ℕ → MvPolynomial (Fin N) ℂ)
    (hc : ∀ i < m, (cf i).IsHomogeneous ((m - i) * k)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : Fin N → ℂ) (g : ℂ),
      g * g ^ m + ∑ i ∈ Finset.range m, (g * MvPolynomial.eval w (cf i)) * g ^ i = 0 →
        ‖g‖ ≤ C * ‖w‖ ^ k := by sorry
