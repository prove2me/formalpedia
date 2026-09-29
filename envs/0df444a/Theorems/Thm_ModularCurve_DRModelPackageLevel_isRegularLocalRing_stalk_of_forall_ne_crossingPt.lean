-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_isRegularLocalRing_stalk_of_forall_ne_crossingPt
-- name    : ModularCurve.DRModelPackageLevel.isRegularLocalRing_stalk_of_forall_ne_crossingPt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/8e658cb2-52a6-525f-b79e-7637f19da31b
-- title:
--   Regularity of stalks off D(q) away from crossing points
-- statement:
--   Fix $N_0,q\in\mathbb N$ with $N_0\neq 0$ and $q$ prime, and a proof $hqN$ that $q\nmid N_0$, and let $\mathfrak X$ be a term of the Deligne–Rapoport model package structure `DRModelPackageLevel N₀ q hqN` for the Igusa-style model `DRLevel.toBase N₀ q : X N₀ q ⟶ Spec (R q)`. Let $O$ be a discrete valuation ring which is an integral domain, equipped with a ring homomorphism $\rho_O\colon R q\to O$ whose maximal ideal satisfies $\mathfrak m_O=(\rho_O(q))$, and let $\kappa$ be an algebraically closed field of characteristic $q$ with decidable equality, together with a ring homomorphism $\mathrm{to}\kappa\colon O\to\kappa$. Write $X_O$ for `DRLevel.XO ρO`, the fibre product of `DRLevel.toBase N₀ q` with $\operatorname{Spec}\rho_O$, whose structure morphism `DRLevel.XO.toBase ρO` to $\operatorname{Spec} O$ is the second projection. Let $z$ be a point of $X_O$ such that (i) $z$ does not lie in the preimage of the basic open $D(\rho_O(q))\subseteq\operatorname{Spec} O$ under that projection, and (ii) for every point $n$ of the fibre product of the two morphisms `𝔛.comp κ (toκ.comp ρO) 0` and `𝔛.comp κ (toκ.comp ρO) 1`, one has $z\neq \mathfrak X.\mathrm{crossingPt}\,\rho_O\,\mathrm{to}\kappa\,n$, the image of $n$ under the map of underlying spaces of the first projection followed by `𝔛.comp κ (toκ.comp ρO) 0` followed by `DRLevel.bcMap ρO toκ`. Then the stalk of the structure sheaf of $X_O$ at $z$ is a regular local ring.
--
--   This is the regularity half of the local analysis of the Deligne–Rapoport model of $X_0(N_0q)$ after base change to a discrete valuation ring with uniformiser $q$: away from the fibres over $D(q)$, the only points where regularity is not asserted are the finitely many crossing points of the two components of the geometric special fibre. It feeds the construction of a resolved model package at this level and the comparison statements [`V3AsmLevel.comp_isInvertible`](thm.html#V3AsmLevel.comp_isInvertible) and [`V3AsmLevel.eta_stalk`](thm.html#V3AsmLevel.eta_stalk).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_isRegularLocalRing_stalk_of_forall_ne_crossingPt.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevelCrossingFrame

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem ModularCurve.DRModelPackageLevel.isRegularLocalRing_stalk_of_forall_ne_crossingPt
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔛 : DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : DRLevel.R q →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)
    (z : ↥(DRLevel.XO (N₀ := N₀) ρO))
    (hz : z ∉ (DRLevel.XO.toBase (N₀ := N₀) ρO) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens))
    (hne : ∀ n : ↥(pullback (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)), z ≠ 𝔛.crossingPt ρO toκ n) :
    IsRegularLocalRing ((DRLevel.XO (N₀ := N₀) ρO).presheaf.stalk z) := by sorry
