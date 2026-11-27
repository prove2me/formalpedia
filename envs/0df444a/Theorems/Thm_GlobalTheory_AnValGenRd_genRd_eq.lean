-- Prove2me | Theorems.Thm_GlobalTheory_AnValGenRd_genRd_eq
-- name    : GlobalTheory.AnValGenRd.genRd_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-27T04:47:17.275799+00:00
-- url     : https://prove2.me/theorems/dcec15f2-7abc-59a9-b78d-dfe1d04699d5
-- title:
--   An Val Gen Rd: gen Rd eq
-- statement:
--   The An Val Gen Rd construction uses the gen Rd eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsHolomorphicGeneratorReadingAutomorphy.lean#L158-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsHolomorphicGeneratorReadingAutomorphy.lean#L158-L162

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsHolomorphicGeneratorReadingAutomorphy
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
open GlobalTheory GlobalTheory.AnValGenRd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open ReciprocityTheory.ChartRestriction.G.TB.ValAt
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)
  {Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L.L φ ε))

theorem GlobalTheory.AnValGenRd.genRd_eq {q : Sp ℂ ⟶ Z} {p : K → Fin g → ℂ} {u : ℂ} (hu : Φ.GenRd φ ε t q p u)
    {j : K → L.L.ι} (hj : ⊤ ≤ q ⁻¹ᵁ LB.wchart L.L φ j) :
    u = valAt' q (LB.wchart L.L φ j) (t.s j).val / ∏ k, Φ.fr (j k) (p k) ^ ε k := by sorry
