-- Prove2me | Theorems.Thm_GlobalTheory_T_invariantOperator_value_triangular_change
-- name    : GlobalTheory.T.invariantOperator_value_triangular_change
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:47:56.696799+00:00
-- url     : https://prove2.me/theorems/deda703c-ec8f-4d47-8c22-3c3ac03f6ff5
-- title:
--   T: invariant Operator value triangular change
-- statement:
--   The T construction uses the invariant Operator value triangular change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/InvariantOperatorValueTriangularChangeStatement.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/InvariantOperatorValueTriangularChangeStatement.lean#L12-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_InvariantOperatorValueTriangularChange
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_InvariantOperatorValueTriangularChangeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.invariantOperator_value_triangular_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) [StarRing (𝓞 E)] (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (d : ℕ) (B : Germ.FB S d (𝓞 E)) (hg : Germ.PS S 2 d), B.IsCanonGauge S hg → ∀ (k n : ℕ) (f : Fin n → MvPowerSeries (Fin 1 × Fin d) S) (uvec uvec' : Lt1 Dw → Fin d → S) (cf : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Fin (Dw.mult τ) → S), (∀ τ i j, i < j → cf τ i j = 0) → (∀ τ i e, uvec' ⟨τ, i⟩ e = ∑ j, cf τ i j * uvec ⟨τ, j⟩ e) → (∀ τ i, IsUnit (cf τ i i)) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, B.nabVal S hg H.w0 k (f b) uvec' (MvPolynomial.monomial (colOf m b) 1) = (∏ ℓ : Lt1 Dw, cf ℓ.1 ℓ.2 ℓ.2 ^ a (ℓ.1, ℓ.2)) * ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, B.nabVal S hg H.w0 k (f b) uvec (MvPolynomial.monomial (colOf m b) 1) := by sorry
