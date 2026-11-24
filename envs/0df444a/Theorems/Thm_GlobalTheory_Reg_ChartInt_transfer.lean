-- Prove2me | Theorems.Thm_GlobalTheory_Reg_ChartInt_transfer
-- name    : GlobalTheory.Reg.ChartInt.transfer
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:18:37.348889+00:00
-- url     : https://prove2.me/theorems/43bd426b-b4b9-4232-9937-16b56f468d8a
-- title:
--   Chart Int: transfer
-- statement:
--   The Chart Int construction uses the transfer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/IntegralityTrivialValuationsOfNormalAffineCharts.lean#L149-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/IntegralityTrivialValuationsOfNormalAffineCharts.lean#L149-L160

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

theorem GlobalTheory.Reg.ChartInt.transfer {la : HeightOneSpectrum (𝓞 c.F)}
    (S : SCharts Xo c la) (j : S.J) (g : FractionRing (S.A j)) (x : S.A j) (hx0 : x ≠ 0)
    (hpts : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra S.O V]
      [Module.Finite S.O V] (φ : S.A j →ₐ[S.O] V), φ x ≠ 0 →
        ∃ (e : ℕ) (r : EReal), 0 < e ∧ ChV φ.toRingHom e g r ∧ 0 ≤ r)
    (qq : Ideal (S.A j)) [qq.IsPrime]
    (hqq : qq ⊔ Ideal.map (algebraMap S.O (S.A j)) (maximalIdeal S.O) ≠ ⊤) :
    ∃ a s : S.A j, s ∉ qq ∧ g * algebraMap (S.A j) (FractionRing (S.A j)) s =
      algebraMap (S.A j) (FractionRing (S.A j)) a := by sorry
