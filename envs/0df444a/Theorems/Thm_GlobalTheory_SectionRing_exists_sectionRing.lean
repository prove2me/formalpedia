-- Prove2me | Theorems.Thm_GlobalTheory_SectionRing_exists_sectionRing
-- name    : GlobalTheory.SectionRing.exists_sectionRing
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:56:25.56146+00:00
-- url     : https://prove2.me/theorems/fbd470f8-d664-456d-bcc6-db56b27ad107
-- title:
--   Section Ring: exists section Ring
-- statement:
--   The Section Ring construction uses the exists section Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsSectionRing.lean#L201-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsSectionRing.lean#L201-L239

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MonomialMemReesAlgIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsSectionRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SectionRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

theorem GlobalTheory.SectionRing.exists_sectionRing :
    (∀ (K : Type) [Field K] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp K) (L : LB X), L.IsLB → ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : Algebra K R) (𝒜 : ℕ → Submodule K R) (_ : GradedAlgebra 𝒜) (Φ : ∀ e : ℕ, (lbPow L e).Sec ≃ 𝒜 e), (∀ e (s s' s'' : (lbPow L e).Sec), (∀ j, s''.f j = s.f j + s'.f j) → Φ e s'' = Φ e s + Φ e s') ∧ (∀ e (a : K) (s s' : (lbPow L e).Sec), (∀ j, s'.f j = constFn p _ a * s.f j) → Φ e s' = a • Φ e s) ∧ (∀ e e' (s : (lbPow L e).Sec) (s' : (lbPow L e').Sec) (s'' : (lbPow L (e + e')).Sec), (∀ j, s''.f j = (show Γ(X, (lbPow L (e + e')).U j) from s.f j) * (show Γ(X, (lbPow L (e + e')).U j) from s'.f j)) → (Φ (e + e') s'' : R) = Φ e s * Φ e' s') ∧ ∀ (j : PUnit → L.ι), ∃ ρ : R →+* Γ(X, (lbPow L 0).U j), (∀ a : K, ρ (algebraMap K R a) = constFn p _ a) ∧ ∀ e (s : (lbPow L e).Sec), ρ (Φ e s) = s.f j) := by sorry
