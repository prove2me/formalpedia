-- Prove2me | Theorems.Thm_GlobalTheory_ChartCmp_Inh_nuLocC_eq_nuAlg
-- name    : GlobalTheory.ChartCmp.Inh.nuLocC_eq_nuAlg
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:48:28.29888+00:00
-- url     : https://prove2.me/theorems/69d2b24e-a11a-4627-a0f9-a0668eafc959
-- title:
--   Inh: nu Loc C eq nu Alg
-- statement:
--   The Inh construction uses the nu Loc C eq nu Alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwoChartAtlas/AdditionLawSecondIdentity.lean#L181-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwoChartAtlas/AdditionLawSecondIdentity.lean#L181-L214

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_Comp1Scalar
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.Inh
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.AdditiveBiext
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]

theorem GlobalTheory.ChartCmp.Inh.nuLocC_eq_nuAlg {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} (Ch : IntChart T io y)
    (B : FB T.V (chD Ch.ch) (𝓞 E)) (hF : B.G.F = Ch.FT) (hA : B.A.act = Ch.actT) (e k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    nuLocC Ch e k a n = letI := io.toAlgebra; nuAlg Dw T B Ch.ch.h Ch.ch.uvec e k a n := by sorry
