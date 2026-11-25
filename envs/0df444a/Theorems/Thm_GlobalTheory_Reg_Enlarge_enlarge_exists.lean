-- Prove2me | Theorems.Thm_GlobalTheory_Reg_Enlarge_enlarge_exists
-- name    : GlobalTheory.Reg.Enlarge.enlarge_exists
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:13:57.611629+00:00
-- url     : https://prove2.me/theorems/a99fbeec-127a-470e-a4fb-10bef25db6ac
-- title:
--   Enlarge: enlarge exists
-- statement:
--   The Enlarge construction uses the enlarge exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralFlagChartEnlargeContainingValue.lean#L221-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIntegralFlagChartEnlargeContainingValue.lean#L221-L235

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_ModelAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralFlagChartEnlargeContainingValue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.Enlarge
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain Polynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
variable {O : Type} [CommRing O] {β : O →+* c.F}
attribute [local instance] Classical.propDecidable

theorem GlobalTheory.Reg.Enlarge.enlarge_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [Algebra O c.F] [IsFractionRing O c.F] (f : Rul Xo c) (P : GlobalTheory.Reg.PChart Xo c (algebraMap O c.F)), (∀ e ∈ P.es, evR Xo c f P.yg ∈ P.R e) → IsIntegral (Algebra.adjoin c.F (P.gens : Set P.Ω)) (evR Xo c f P.yg) → ∃ P' : GlobalTheory.Reg.PChart Xo c (algebraMap O c.F), evR Xo c f P'.yg ∈ Algebra.adjoin c.F (P'.gens : Set P'.Ω) ∧ ∀ (L : Type) [Field L] [Algebra c.F L] (W : ValuationSubring L), (∀ a : O, algebraMap c.F L (algebraMap O c.F a) ∈ W) → ∀ y : FrPt Xo c L, P.Catches W y → P'.Catches W y := by sorry
