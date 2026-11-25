-- Prove2me | Theorems.Thm_GlobalTheory_Reg_TrivBound_comb_triv
-- name    : GlobalTheory.Reg.TrivBound.comb_triv
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:18:43.006054+00:00
-- url     : https://prove2.me/theorems/ce2525a2-ae02-4244-819e-701213bb97e9
-- title:
--   Triv Bound: comb triv
-- statement:
--   The Triv Bound construction uses the comb triv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/CombinedBoundAtTrivialValuationsOfCharts.lean#L494-L563
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/CombinedBoundAtTrivialValuationsOfCharts.lean#L494-L563

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
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_CombinedBoundAtTrivialValuationsOfCharts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.TrivBound
open IsLocalRing Formalism.L2.PjFree
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
set_option maxHeartbeats 1000000

theorem GlobalTheory.Reg.TrivBound.comb_triv {la : HeightOneSpectrum (𝓞 c.F)}
    (S : SCharts Xo c la) (hQ : S.CovQ) {m : ℕ} (ws : Fin m → Rul Xo c) (hF : S.FamW ws)
    {aL nL} (hws : ∀ k, ws k ∈ sec Xo c aL nL)
    {aE nE} {et : Rul Xo c} (het : et ∈ sec Xo c aE nE)
    (nu c' : ℝ) (hc' : 0 ≤ c')
    (hyp : ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v et ∧
      (v et ≠ ⊤ → (⨅ k, v (ws k)) ≤ (nu : EReal) + (c' : EReal) * v et)) :
    ∀ q ∈ trivSet Xo c, q et ≠ ⊤ → (⨅ k, q (ws k)) ≤ (c' : EReal) * q et := by sorry
