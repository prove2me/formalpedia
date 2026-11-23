-- Prove2me | Theorems.Thm_GlobalTheory_ZH_CrdCalc_crd_calculus
-- name    : GlobalTheory.ZH.CrdCalc.crd_calculus
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:27:17.445739+00:00
-- url     : https://prove2.me/theorems/a5dc406a-dc3d-478a-bc67-d2d6aed7ff6d
-- title:
--   Crd Calc: crd calculus
-- statement:
--   The Crd Calc construction uses the crd calculus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUnitCharts.lean#L135-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUnitCharts.lean#L135-L138

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnitCharts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
noncomputable section
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.CrdCalc
variable {R : Type} [CommRing R] {X : Scheme.{0}}
variable {H : LB X} {J : Type} {s : J → H.Sec}

theorem GlobalTheory.ZH.CrdCalc.crd_calculus : (∀ (X : Scheme.{0}) (H : LB X) (J : Type) (s : J → H.Sec), H.IsLB → (∀ (R : Type) [CommRing R] [IsLocalRing R] (x : Sp R ⟶ X), (∃ v, Crd H s x v) ∧ (∀ v v', Crd H s x v → Crd H s x v' → ∃ c : Rˣ, ∀ j, v' j = (c : R) * v j) ∧ ∀ v j, Crd H s x v → (IsUnit (v j) ↔ ⊤ ≤ x ⁻¹ᵁ Out.nonzeroLocus (s j))) ∧ (∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (x : Sp R ⟶ X) (v : J → R), Crd H s x v → Crd H s (spMap φ ≫ x) (fun j => φ (v j))) ∧ (∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : J → R) (c : Rˣ), Crd H s x v → Crd H s x (fun j => (c : R) * v j)) ∧ ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : J → R) (i j : J) (W : X.Opens) (r : Γ(X, W)), Crd H s x v → IsRatio (s j) (s i) W r → ⊤ ≤ x ⁻¹ᵁ W → v j = valR x W r * v i) := by sorry
