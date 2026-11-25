-- Prove2me | Theorems.Thm_GlobalTheory_EigenDer_dof_eq_of_eigen
-- name    : GlobalTheory.EigenDer.dof_eq_of_eigen
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:58:16.675146+00:00
-- url     : https://prove2.me/theorems/6b8333c8-34fd-48bc-ae2c-5179b92b6771
-- title:
--   Eigen Der: dof eq of eigen
-- statement:
--   The Eigen Der construction uses the dof eq of eigen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SubstMapAlgebraMap.lean#L124-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SubstMapAlgebraMap.lean#L124-L178

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_HasSubstAddSqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsNilpotentOfMemKerJetTruncR
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SubstMapAlgebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε LPow ThetaGrp IsActOf WeilIs translT GlobalFnsSt)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Good val sval gs)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.EigenDer
variable {R : Type} [CommRing R]

theorem GlobalTheory.EigenDer.dof_eq_of_eigen : JetAlgSt → RepSt → SerSt → ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (d : ℕ) (x : Fam G (Fin d)), IsUnivChart G d x → ∀ Gl : FGLaw R d, IsLawOf x Gl.F → ∀ (U : G.left.Opens), ⊤ ≤ η[G].left ⁻¹ᵁ U → ∀ (s : Γ(G.left, U)) (f : PS R 1 d), IsSer1 x U s f → ∀ (v : Fin d → R) (y : R) (φ : JetR R (Fin d) 1 →ₐ[R] DualNumber R), (∀ i, φ (zR 1 i) = TrivSqZeroExt.inr (v i)) → (∀ (A : Type) [CommRing A] [Algebra R A] (c : DualNumber R →ₐ[R] A) (r : sp (R₀ := R) A ⟶ G), ⊤ ≤ r.left ⁻¹ᵁ U → ⊤ ≤ (r * (spMap c ≫ spMap φ ≫ x 1)).left ⁻¹ᵁ U → fnVal (r * (spMap c ≫ spMap φ ≫ x 1)).left U s = c (1 + TrivSqZeroExt.inr y) * fnVal r.left U s) → Dof Gl.F v f = C y * f := by sorry
