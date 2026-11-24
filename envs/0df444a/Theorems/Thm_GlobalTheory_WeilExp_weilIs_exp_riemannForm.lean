-- Prove2me | Theorems.Thm_GlobalTheory_WeilExp_weilIs_exp_riemannForm
-- name    : GlobalTheory.WeilExp.weilIs_exp_riemannForm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:23:32.693059+00:00
-- url     : https://prove2.me/theorems/afcb104b-c2f9-4779-bd5e-f8ee8279c433
-- title:
--   Weil Exp: weil Is exp riemann Form
-- statement:
--   The Weil Exp construction uses the weil Is exp riemann Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/WeilIsExpRiemannForm.lean#L135-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/WeilIsExpRiemannForm.lean#L135-L224

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_WeilIsExpRiemannForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.WeilExp

theorem GlobalTheory.WeilExp.weilIs_exp_riemannForm : Out.WeilSt → (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (X : Over (Sp ℂ)), IsReduced X.left → LocallyOfFiniteType X.hom → ∀ (U : X.left.Opens) (f f' : Γ(X.left, U)), (∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U → valAt' x.left U f = valAt' x.left U f') → f = f') → (∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ), Smooth p → IsReduced X) → (∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))))) * u.fr i (z + l)) → ∀ (k : ℕ) (a : u.Λ), 0 < k → ∀ (T : Over (Sp ℂ)) (p : (𝟙_ (Over (Sp ℂ)) ⟶ T)) (θ : Out.ThetaGrp P.A P.L k T), p ≫ θ.pt = u.ex ((k : ℂ)⁻¹ • (a : Fin P.g → ℂ)) → ∃ C : ℂ, ∀ (j : Fin 2 → P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j 0) → ⊤ ≤ (u.ex (z + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ))).left ⁻¹ᵁ P.L.U (j 1) → valAt' (lift p (u.ex z)).left _ (θ.φ.s j).val * u.fr (j 1) (z + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ)) ^ k = C * cexp (-(Real.pi * (z ⬝ᵥ Hm.mulVec (star (a : Fin P.g → ℂ))))) * u.fr (j 0) z ^ k) → (∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))))) * u.fr i (z + l)) → ∀ (k : ℕ) (a b : u.Λ) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef a b : ℂ) / k) → Out.WeilIs P.A P.L k (u.ex ((k : ℂ)⁻¹ • (a : Fin P.g → ℂ))) (u.ex ((k : ℂ)⁻¹ • (b : Fin P.g → ℂ))) (unitOn c)) := by sorry
