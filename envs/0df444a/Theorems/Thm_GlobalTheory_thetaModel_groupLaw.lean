-- Prove2me | Theorems.Thm_GlobalTheory_thetaModel_groupLaw
-- name    : GlobalTheory.thetaModel_groupLaw
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:19.499031+00:00
-- url     : https://prove2.me/theorems/76addcab-411d-451a-a12a-26aefefffb37
-- title:
--   Global Theory: theta Model group Law
-- statement:
--   The Global Theory construction uses the theta Model group Law property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/LocallyOfFiniteTypeTensor.lean#L228-L353
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/LocallyOfFiniteTypeTensor.lean#L228-L353

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_LocallyOfFiniteTypeTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
open ThetaModelGroup

theorem GlobalTheory.thetaModel_groupLaw : (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Set E) (X
    Y : Over (Sp ℂ)) (a : E → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (b : E → (𝟙_ (Over (Sp ℂ)) ⟶ Y)), (∀ (U
    : (X).left.Opens) (f : Γ((X).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (a
    w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (a w).left U f) {w | w ∈ W ∧ ⊤ ≤ (a
    w).left ⁻¹ᵁ U}) → (∀ (U : (Y).left.Opens) (f : Γ((Y).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (b
    w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (b w).left U f) {w | w ∈ W ∧ ⊤ ≤ (b
    w).left ⁻¹ᵁ U}) → (∀ (U : (X ⊗ Y).left.Opens) (f : Γ((X ⊗ Y).left, U)), IsOpen {w
    | w ∈ W ∧ ⊤ ≤ ((fun w => lift (a w) (b w))
    w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' ((fun w => lift (a w) (b w))
    w).left U f) {w | w ∈ W ∧ ⊤ ≤ ((fun w => lift (a w) (b w)) w).left ⁻¹ᵁ U})) → (∀ (X : Over (Sp
    ℂ)), IsReduced X.left → LocallyOfFiniteType X.hom → ∀ (U : X.left.Opens) (f f' : Γ(X.left,
    U)), (∀ x : (𝟙_ (Over (Sp ℂ)) ⟶
    X), ⊤ ≤ (x).left ⁻¹ᵁ U → valAt' x.left U f = valAt' x.left U f') → f = f') → (∀ (X Y : Over (Sp
    ℂ)), IsReduced Y.left → LocallyOfFiniteType Y.hom → ∀ F : (𝟙_ (Over (Sp ℂ)) ⟶ Y) → (𝟙_ (Over (Sp
    ℂ)) ⟶ X), (∀ y : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ∃ (U : Y.left.Opens) (D
    : X.left.Opens), ⊤ ≤ (y).left ⁻¹ᵁ U ∧ IsAffineOpen D ∧ (∀ y' : (𝟙_ (Over (Sp ℂ)) ⟶
    Y), ⊤ ≤ (y').left ⁻¹ᵁ U → ⊤ ≤ (F y').left ⁻¹ᵁ D) ∧ ∀ φ : Γ(X.left, D), ∃ ρ : Γ(Y.left,
    U), ∀ y' : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ (y').left ⁻¹ᵁ U → valAt' y'.left U ρ = valAt' (F
    y').left D φ) → ∃! m : Y ⟶ X, ∀ y, y ≫ m = F y) → (∀ (X Y : Over (Sp
    ℂ)), IsReduced X.left → IsReduced Y.left → LocallyOfFiniteType X.hom → LocallyOfFiniteType Y.hom → IsReduced (X
    ⊗ Y).left) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin
    g) → ∀ N : ℕ, 1 ≤ N → ∀ f f' : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n'
    : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ
    ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → (Differentiable ℂ f' ∧ ∀ (n n'
    : Fin g → ℤ) z, f' (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ
    ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f' z) → ∃ (n : ℕ) (h k : Fin n → (Fin g →
    ℂ) → ℂ), (∀ i, (Differentiable ℂ (h i) ∧ ∀ (n n' : Fin g → ℤ) z, (h i) (z + τ *ᵥ ofIntVec n +
    ofIntVec n') = eC (-((2 * N : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ
    z)) * (h i) z) ∧ (Differentiable ℂ (k i) ∧ ∀ (n n' : Fin g → ℤ) z, (k i) (z + τ *ᵥ ofIntVec n +
    ofIntVec n') = eC (-((2 * N : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ
    z)) * (k i) z)) ∧ ∀ z w, f (z + w) * f' (z - w) = ∑ i, h i z * k i w) → (∀ (g : ℕ) (τ
    : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin
    g) → ∀ N : ℕ, 1 ≤ N → (∀ c : Fin g → Fin N, (Differentiable ℂ (fun z => theta (fun i => ((c i
    : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ (n n'
    : Fin g → ℤ) z, (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) (z
    + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 +
    ofIntVec n ⬝ᵥ z)) * (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) •
    τ)) z)) ∧ LinearIndependent ℂ (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => theta (fun i => ((c i
    : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin
    g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → ∀ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n
    n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ
    ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → f ∈ Submodule.span ℂ (Set.range (fun (c
    : Fin g → Fin N) (z : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N
    : ℂ) • τ)))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin
    g) → ∀ N : ℕ, 2 ≤ N → ∀ z, ∃ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n'
    : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ
    ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) ∧ f z ≠ 0) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin
    g) ℂ), τ ∈ SiegelH (Fin g) → DiscreteTopology (periodLattice
    τ) ∧ Submodule.span ℝ (periodLattice τ : Set (Fin g →
    ℂ)) = ⊤ ∧ ∀ n n' : Fin g → ℤ, τ *ᵥ ofIntVec n + ofIntVec n' = 0 → n = 0 ∧ n' = 0) → (∀ (g
    : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∀ (X : Over (Sp
    ℂ)) (ex : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (D : (Fin g → Fin
    N) → X.left.Opens), (IsIntegral X.left ∧ IsProper X.hom ∧ Function.Surjective ex ∧
    (∀ z z', ex z = ex z' ↔ z - z' ∈ periodLattice τ) ∧ (∀ (U : (X).left.Opens) (f : Γ((X).left,
    U)), IsOpen {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex
    w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (ex w).left U f) {w | w ∈ (Set.univ
    : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U}) ∧ (∀ c, IsAffineOpen (D c) ∧ ringKrullDim Γ(X.left,
    D c) ≤ g ∧ (∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ D c ↔ theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) •
    z) ((N : ℂ) • τ) ≠ 0) ∧ ∃ r : (Fin g → Fin N) → Γ(X.left, D c), (∀ c' z, theta (fun i => ((c i
    : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) ≠ 0 → valAt' (ex z).left (D c) (r
    c') = theta (fun i => ((c' i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) / theta (fun i => ((c
    i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ f : Γ(X.left, D c), ∃ F : MvPolynomial (Fin
    g → Fin N) ℂ, f = MvPolynomial.eval₂ (RingHom.comp (X.hom.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso
    (CommRingCat.of ℂ)).inv.hom) r F) ∧ (⨆ c, D c = ⊤)) → (∀ (d : ℕ) (p q : (Fin g →
    ℂ) → ℂ), (Differentiable ℂ p ∧ ∀ (n n' : Fin g → ℤ) z, p (z + τ *ᵥ ofIntVec n + ofIntVec
    n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ
    z)) * p z) → (Differentiable ℂ q ∧ ∀ (n n' : Fin g → ℤ) z, q (z + τ *ᵥ ofIntVec n + ofIntVec
    n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ
    z)) * q z) → ∃ (U : X.left.Opens) (φ : Γ(X.left, U)), ∀ z, (⊤ ≤ (ex z).left ⁻¹ᵁ U ↔ q z ≠
    0) ∧ (q z ≠ 0 → valAt' (ex z).left U φ = p z / q z)) → ∃ (_
    : GrpObj X), IsCommMonObj X ∧ ∀ z w, ex (z + w) = ex z * ex w) := by sorry
