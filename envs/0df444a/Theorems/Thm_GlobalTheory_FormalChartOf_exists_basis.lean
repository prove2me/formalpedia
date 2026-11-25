-- Prove2me | Theorems.Thm_GlobalTheory_FormalChartOf_exists_basis
-- name    : GlobalTheory.FormalChartOf.exists_basis
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:45:09.03739+00:00
-- url     : https://prove2.me/theorems/5303d4b5-46ad-49fa-91c8-1ea9632444d9
-- title:
--   Formal Chart Of: exists basis
-- statement:
--   The Formal Chart Of construction uses the exists basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsFormalChart.lean#L183-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsFormalChart.lean#L183-L267

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsFormalChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.FormalChartOf
variable {R₀ : Type} [CommRing R₀]
variable {G : Over (Spec (CommRingCat.of R₀))} [GrpObj G] {g : ℕ}
  (x : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (Fin g → S) → (sp (R₀ := R₀) S ⟶ G))
  (h0 : ∀ (S : Type) [CommRing S] [Algebra R₀ S], x S 0 = 1)
  (hnat : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S']
    (φ : S →ₐ[R₀] S') (a : Fin g → S),
    (∀ i, IsNilpotent (a i)) → spMap φ ≫ x S a = x S' (fun i => φ (a i)))
  (hinj : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) →
    (∀ i, IsNilpotent (b i)) → x S a = x S b → a = b)
  (hsurj : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S']
    (ρ : S →ₐ[R₀] S'), Function.Surjective ρ →
    (∀ a ∈ RingHom.ker ρ, IsNilpotent a) → ∀ z : sp (R₀ := R₀) S ⟶ G, spMap ρ ≫ z = 1 →
    ∃ a : Fin g → S, (∀ i, a i ∈ RingHom.ker ρ) ∧ z = x S a)
variable [IsLocalRing R₀] (B : BX R₀) (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G))
  (he : ∀ R, Function.Bijective (e R)) (hadd : ∀ R x y, e R (x + y) = e R x * e R y)
  (hen : ∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x)
include h0 hnat hinj hsurj he hadd hen

theorem GlobalTheory.FormalChartOf.exists_basis : ∃ gb : Module.Basis (Fin g) R₀ B.gg, ∀ w : B.gg,
    e (dualL R₀) (B.tg (dualProj R₀) dualProj_sqZero (w ⊗ₜ epsK R₀)) =
      x (DualNumber R₀) (fun k => TrivSqZeroExt.inr (gb.repr w k)) := by sorry
