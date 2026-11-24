-- Prove2me | Theorems.Thm_GlobalTheory_Reg_evR_eq_map_of_test_point
-- name    : GlobalTheory.Reg.evR_eq_map_of_test_point
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:21:19.920208+00:00
-- url     : https://prove2.me/theorems/6b25f44e-4d0a-4b5f-979c-a1e594d961cf
-- title:
--   Reg: ev R eq map of test point
-- statement:
--   The Reg construction uses the ev R eq map of test point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/SectionEqZeroOfGenericFramedPointValues.lean#L13-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/SectionEqZeroOfGenericFramedPointValues.lean#L13-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_Reframe
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_ModelAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_SectionEqZeroOfGenericFramedPointValues
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
open GlobalTheory GlobalTheory.Reg

theorem GlobalTheory.Reg.evR_eq_map_of_test_point {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (hL : EvLaws Xo c) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {g : Rul Xo c} (hg : g ∈ sec Xo c a n) {S : Type} [CommRing S] [Algebra c.F S] (p : TRing c.F)
    (φ : p.R →ₐ[c.F] S) (y : FrPt Xo c p.R) (w : FrPt Xo c S) (hw : FrMap φ y w) :
    evR Xo c g w = φ (g p y) := by sorry
