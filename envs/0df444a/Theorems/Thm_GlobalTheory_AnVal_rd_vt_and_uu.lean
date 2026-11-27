-- Prove2me | Theorems.Thm_GlobalTheory_AnVal_rd_vt_and_uu
-- name    : GlobalTheory.AnVal.rd_vt_and_uu
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-27T05:47:10.122489+00:00
-- url     : https://prove2.me/theorems/fbcf6eb5-7561-47ac-a29c-843a919c8d3d
-- title:
--   An Val: rd vt and uu
-- statement:
--   The An Val construction uses the rd vt and uu property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExpNsmulEqPowVt.lean#L19-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExpNsmulEqPowVt.lean#L19-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NormalisedPullbackMulNReadsThetaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_SymmetricLiftOddOrderActsAsTranslationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExpNsmulEqPowVt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AnVal

theorem GlobalTheory.AnVal.rd_vt_and_uu : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), (∀ a ∈ Φ.lat, Φ.χ a ^ 2 = 1) → ∀ (N : ℕ), Odd N → ∀ (s : LB.Sec (LPow A L.L 1 (Over.mk x0))) (θ : (Fin g → ℂ) → ℂ), Φ.Rd 1 s θ → (∀ (ok : (Over.mk x0 ⟶ A) → Prop) (t : Over.mk x0 ⟶ A) (F : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) (Over.mk x0))), IsVtOver A L N ok s t F → (∀ t', ok t' → t' ^ N = t → t' ^ (N ^ 2) = 1) → ∃ x δ : Fin g → ℂ, δ ∈ Φ.lat ∧ ((N : ℂ) ^ 2) • x = (2 : ℂ) • δ ∧ ok (Φ.e x) ∧ Φ.e x ^ N = t ∧ Φ.Rd ((N : ℤ) ^ 2) F (fock Φ.Hm ((N : ℤ) ^ 2) x fun z => θ ((N : ℂ) • z))) ∧ ∀ (x₁ δ₁ x₂ δ₂ : Fin g → ℂ) (F : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) (Over.mk x0))), δ₁ ∈ Φ.lat → ((N : ℂ) ^ 2) • x₁ = (2 : ℂ) • δ₁ → δ₂ ∈ Φ.lat → ((N : ℂ) ^ 2) • x₂ = (2 : ℂ) • δ₂ → IsUUOver A L N s (Φ.e x₁) (Φ.e x₂) F → Φ.Rd ((N : ℤ) ^ 2) F (fock Φ.Hm ((N : ℤ) ^ 2) x₂ (fock Φ.Hm ((N : ℤ) ^ 2) x₁ fun z => θ ((N : ℂ) • z))) := by sorry
