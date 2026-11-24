-- Prove2me | Theorems.Thm_GlobalTheory_T_jetPoint_add_sqZero_eq_prod_mul_tangent
-- name    : GlobalTheory.T.jetPoint_add_sqZero_eq_prod_mul_tangent
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:22:00.931746+00:00
-- url     : https://prove2.me/theorems/d3ff1043-7001-48f2-ba9f-b75d218d2ce9
-- title:
--   T: jet Point add sq Zero eq prod mul tangent
-- statement:
--   The T construction uses the jet Point add sq Zero eq prod mul tangent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/JetPointAddSqZeroEqProdMulTangentStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/JetPointAddSqZeroEqProdMulTangentStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetPointAddSqZeroEqProdMulTangent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetPointAddSqZeroEqProdMulTangentStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.T.jetPoint_add_sqZero_eq_prod_mul_tangent : ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (d : ℕ) (v : Fin d → (epsR R ⟶ G)), IsLieBasis v → ∀ (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G), (∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m) → (∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1) → (∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j) → ∀ (A : Type) [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (J : Ideal A), J * RingHom.ker aug = ⊥ → J ≤ RingHom.ker aug → ∀ (m : ℕ) (ψ ψ' : JetR R (Fin d) m →ₐ[R] A), aug.comp ψ = jetAug R (Fin d) m → aug.comp ψ' = jetAug R (Fin d) m → ∀ e : Fin d → (DualNumber R →ₐ[R] A), (∀ j, e j (TrivSqZeroExt.inr 1) ∈ J) → (∀ j, ψ' (zR m j) = ψ (zR m j) + e j (TrivSqZeroExt.inr 1)) → spMap ψ' ≫ x m = (∏ j, (spMap (e j) ≫ v j : sp (R₀ := R) A ⟶ G)) * (spMap ψ ≫ x m) := by sorry
