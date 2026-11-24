-- Prove2me | Theorems.Thm_GlobalTheory_Reg_ChartInt_nonneg_at
-- name    : GlobalTheory.Reg.ChartInt.nonneg_at
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:29:56.616321+00:00
-- url     : https://prove2.me/theorems/a18591fe-8f1e-48bf-be80-41f6b9c5b94d
-- title:
--   Chart Int: nonneg at
-- statement:
--   The Chart Int construction uses the nonneg at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/IntegralityTrivialValuationsOfNormalAffineCharts.lean#L162-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/IntegralityTrivialValuationsOfNormalAffineCharts.lean#L162-L172

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelC
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegQFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FnTrdegOf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RealPtGeo
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllProofFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_IntegralityTrivialValuationsOfNormalAffineCharts
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
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.ChartInt
open IsLocalRing Formalism.L2.PjFree
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem GlobalTheory.Reg.ChartInt.nonneg_at {la : HeightOneSpectrum (𝓞 c.F)}
    (S : SCharts Xo c la) {a n} {F : Rul Xo c} (hF : F ∈ sec Xo c a n)
    (h0 : ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) (j : S.J) (x : S.A j) (hxE : x ∈ S.Eb j)
    (hx0 : x ≠ 0) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra S.O V]
    (φ : S.A j →ₐ[S.O] V) (e : ℕ) (rr : EReal) (hch : ChV φ.toRingHom e (S.ch j F) rr)
    (hqq : (maximalIdeal V).comap φ.toRingHom ⊔ Ideal.map (algebraMap S.O (S.A j)) (maximalIdeal S.O) ≠ ⊤) :
    0 ≤ rr := by sorry
