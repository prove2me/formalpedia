-- Prove2me | Theorems.Thm_GlobalTheory_NabLinear_nabVal_C_mul
-- name    : GlobalTheory.NabLinear.nabVal_C_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:30:40.902116+00:00
-- url     : https://prove2.me/theorems/15f9b10b-5e1a-4cb2-baba-4bb679f78e4d
-- title:
--   Nab Linear: nab Val C mul
-- statement:
--   The Nab Linear construction uses the nab Val C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ConnectionLinearInSection.lean#L49-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ConnectionLinearInSection.lean#L49-L58

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
variable {k : Type} [CommRing k] {d : ℕ}

theorem GlobalTheory.NabLinear.nabVal_C_mul [Algebra ℚ k] {R : Type} [CommRing R] [Algebra R k] {O : Type} [CommRing O] [StarRing O]
    (B : Germ.FB R d O) (h : PS k 2 d) (w0 : O) (q : ℕ) (c : k) (f : PS k 1 d) {κ : Type} [Fintype κ]
    (u : κ → Fin d → k) (P : MvPolynomial κ k) :
    B.nabVal k h w0 q (MvPowerSeries.C c * f) u P = c * B.nabVal k h w0 q f u P := by sorry
