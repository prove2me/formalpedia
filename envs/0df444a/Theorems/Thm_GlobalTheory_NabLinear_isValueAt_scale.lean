-- Prove2me | Theorems.Thm_GlobalTheory_NabLinear_isValueAt_scale
-- name    : GlobalTheory.NabLinear.isValueAt_scale
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:30:47.047934+00:00
-- url     : https://prove2.me/theorems/956865bb-d725-44ec-9db8-5f10f1f60233
-- title:
--   Nab Linear: is Value At scale
-- statement:
--   The Nab Linear construction uses the is Value At scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ConnectionLinearInSection.lean#L79-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ConnectionLinearInSection.lean#L79-L111

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThExpBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDVal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ConnectionLinearInSection
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
open GlobalTheory GlobalTheory.NabLinear
variable {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left) (a : ℤ)

theorem GlobalTheory.NabLinear.isValueAt_scale {T T' : Over S0} (g : T' ⟶ T) {F F' : LB.Sec (LPow A L a T)} {r : Γ(T.left, ⊤)}
    (hF : ∀ j, F'.f j = liftFun A _ (T := T) r * F.f j) {F₁ F₂ : LB.Sec (LPow A L a T')}
    (h₁ : IsPullSec A L a (g ▷ A) (whiskerRight_snd g A) F F₁)
    (h₂ : IsPullSec A L a (g ▷ A) (whiskerRight_snd g A) F' F₂) {z : T' ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T'.left) (K := Fin 1) (fun _ => z.left) (fun _ => a))} {v : Γ(T'.left, ⊤)}
    (hv : IsValueAt A L a F₁ z τ v) : IsValueAt A L a F₂ z τ (g.left.appTop.hom r * v) := by sorry
