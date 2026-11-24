-- Prove2me | Theorems.Thm_GlobalTheory_Reg_PChart_exists_refine
-- name    : GlobalTheory.Reg.PChart.exists_refine
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:19:33.599229+00:00
-- url     : https://prove2.me/theorems/7a319048-15bc-42e1-8478-df762be180c7
-- title:
--   PChart: exists refine
-- statement:
--   The PChart construction uses the exists refine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsRefinedCoveringChartFamily.lean#L44-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsRefinedCoveringChartFamily.lean#L44-L109

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_ModelAt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_AdjoinRatiosOfSpanEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_NaturalRuleValueBaseChangeOfIsReducedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_SpanEvalEqTopOfNoCommonZeroReducedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsRefinedCoveringChartFamily
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
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory GlobalTheory.Reg
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
set_option maxHeartbeats 800000

theorem GlobalTheory.Reg.PChart.exists_refine (hL : EvLaws Xo c) {O : Type} [CommRing O] {β : O →+* c.F} (P : PChart Xo c β)
    {m : ℕ} (ws : Fin m → Rul Xo c)
    (hw : ∀ e (he : e ∈ P.es) i, ((evR Xo c (ws i) (P.y e he) : P.R e) : P.Ω) = evR Xo c (ws i) P.yg)
    (hspan : ∀ e (he : e ∈ P.es), Ideal.span (Set.range fun i => (evR Xo c (ws i) (P.y e he) : P.R e)) = ⊤)
    (k : Fin m) (hk : evR Xo c (ws k) P.yg ≠ 0) :
    ∃ P' : PChart Xo c β, P'.Fam ws ∧
      ∀ (L : Type) [Field L] [Algebra c.F L] (W : ValuationSubring L) (y : FrPt Xo c L)
        (e : P.Ω) (he : e ∈ P.es) (ψ : P.R e →ₐ[c.F] L) (z : FrPt Xo c L) (t : Ix Dw → Lˣ),
        (∀ g : P.R e, (g : P.Ω) ∈ P.gens → ψ g ∈ W) → FrMap ψ (P.y e he) z → FrBor t y z →
        ψ (evR Xo c (ws k) (P.y e he)) ≠ 0 →
        (∀ i, ψ (evR Xo c (ws i) (P.y e he)) / ψ (evR Xo c (ws k) (P.y e he)) ∈ W) → P'.Catches W y := by sorry
