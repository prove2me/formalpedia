-- Prove2me | Theorems.Thm_GlobalTheory_IntegralCusp_evHom_aeval
-- name    : GlobalTheory.IntegralCusp.evHom_aeval
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:18:44.413129+00:00
-- url     : https://prove2.me/theorems/b8ebbe12-20a5-593a-8a2c-a881d54cec52
-- title:
--   Integral Cusp: ev Hom aeval
-- statement:
--   The Integral Cusp construction uses the ev Hom aeval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/BddOfMemHolSub.lean#L146-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/BddOfMemHolSub.lean#L146-L161

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
variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l}

theorem GlobalTheory.IntegralCusp.evHom_aeval {σ : c.F →+* ℂ} (y : _root_.Formalism.L2.Pj.FrPt Xo c (_root_.Formalism.L2.Pj.CAt σ))
    (hy : _root_.Formalism.L2.Pj.FromTest (K := c.F) (fun S _ _ => _root_.Formalism.L2.Pj.FrPt Xo c S) (fun φ y z => _root_.Formalism.L2.Pj.FrMap φ y z) y) {N : ℕ}
    (w : Fin N → _root_.Formalism.L2.Pj.Rul Xo c) (p : MvPolynomial (Fin N) c.F) :
    _root_.GlobalTheory.IntegralCusp.evHom y hy (MvPolynomial.aeval w p) =
      MvPolynomial.eval (fun i => _root_.GlobalTheory.IntegralCusp.evHom y hy (w i))
        (MvPolynomial.map σ p) := by sorry
