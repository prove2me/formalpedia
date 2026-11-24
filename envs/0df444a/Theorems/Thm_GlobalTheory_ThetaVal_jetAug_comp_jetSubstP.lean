-- Prove2me | Theorems.Thm_GlobalTheory_ThetaVal_jetAug_comp_jetSubstP
-- name    : GlobalTheory.ThetaVal.jetAug_comp_jetSubstP
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:08:01.365748+00:00
-- url     : https://prove2.me/theorems/e76c2113-f215-4e94-8714-4120c73876da
-- title:
--   Theta Val: jet Aug comp jet Subst P
-- statement:
--   The Theta Val construction uses the jet Aug comp jet Subst P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FrameRigidificationOfCanonicalAxes.lean#L19-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FrameRigidificationOfCanonicalAxes.lean#L19-L26

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBGen
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBPrim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FrameRigidificationOfCanonicalAxes
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

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
open GlobalTheory GlobalTheory.ThetaVal

theorem GlobalTheory.ThetaVal.jetAug_comp_jetSubstP {S A B : Type} [CommRing S] (m : ℕ) (φ : A → MvPolynomial B S) :
    (jetAug : Jet S B m →ₐ[S] S).comp (jetSubstP m φ) = (jetAug : Jet S A m →ₐ[S] S) := by sorry
