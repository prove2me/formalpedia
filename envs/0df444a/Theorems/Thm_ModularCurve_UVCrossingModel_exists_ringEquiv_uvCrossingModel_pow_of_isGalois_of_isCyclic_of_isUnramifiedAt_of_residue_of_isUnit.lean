-- Prove2me | Theorems.Thm_ModularCurve_UVCrossingModel_exists_ringEquiv_uvCrossingModel_pow_of_isGalois_of_isCyclic_of_isUnramifiedAt_of_residue_of_isUnit
-- name    : ModularCurve.UVCrossingModel.exists_ringEquiv_uvCrossingModel_pow_of_isGalois_of_isCyclic_of_isUnramifiedAt_of_residue_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/2d827f81-99a8-5c18-ac16-fb942eceb02f
-- title:
--   Tame cyclic degree-n covers of the node of thickness mn
-- statement:
--   Let $W$ be a commutative local domain which is a discrete valuation ring, complete with respect to the adic topology of its maximal ideal, let $\pi \in W$ be irreducible, and let $m, n \ge 1$ be integers whose images in $W$ are both units. Write $R_0 := \mathrm{UVCrossingModel}\,W\,(\pi^{mn}) = W[[X_0,X_1]]/(X_0X_1 - \pi^{mn})$ for the two-variable power series ring modulo the crossing relation, and $\mathrm{const}$ for the map sending $w \in W$ to the class of the constant series $w$. Let $B$ be a Noetherian local integrally closed domain which is an $R_0$-algebra, module-finite over $R_0$ and with injective structure map, let $K_0$ be a fraction field of $R_0$, and let $F$ be a field that is simultaneously a fraction field of $B$ and an extension of $K_0$, all structure maps being compatible in the evident towers over $R_0$. Assume $F/K_0$ is finite Galois with cyclic automorphism group and $[F:K_0] = n$; assume that for every prime ideal $\mathfrak p$ of $B$ whose contraction to $R_0$ has height $1$, the algebra $B$ is unramified over $R_0$ at $\mathfrak p$; and assume that every $b \in B$ is congruent, modulo the maximal ideal of $B$, to the image in $B$ of $\mathrm{const}(\pi^{mn})(w)$ for some $w \in W$. Then there is a ring isomorphism $e : B \to W[[X_0,X_1]]/(X_0X_1 - \pi^{m})$ carrying the image in $B$ of $\mathrm{const}(\pi^{mn})(w)$ to $\mathrm{const}(\pi^{m})(w)$ for every $w \in W$.
--
--   This is a Kummer-descent statement in the style of Abhyankar's lemma: a tame cyclic cover of degree $n$ of the formal node of thickness $mn$, unramified away from the closed point and trivial on residue constants, is again a formal node, of thickness $m$. No roots of unity are assumed present in $W$; instead $m$ and $n$ are required to be invertible, which suffices after an unramified (étale) enlargement of $W$. It feeds the corresponding statement for adic completions, [`ModularCurve.UVCrossingModel.exists_ringEquiv_adicCompletion_uvCrossingModel_pow_of_isInvariant_of_card_inertia_eq_of_isUnit`](thm.html#ModularCurve.UVCrossingModel.exists_ringEquiv_adicCompletion_uvCrossingModel_pow_of_isInvariant_of_card_inertia_eq_of_isUnit), used in the analysis of the local structure of models of modular curves at a node.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_UVCrossingModel_exists_ringEquiv_uvCrossingModel_pow_of_isGalois_of_isCyclic_of_isUnramifiedAt_of_residue_of_isUnit.lean

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.UVCrossingModel

theorem ModularCurve.UVCrossingModel.exists_ringEquiv_uvCrossingModel_pow_of_isGalois_of_isCyclic_of_isUnramifiedAt_of_residue_of_isUnit
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hnW : IsUnit (n : W))
    (hmW : IsUnit (m : W))
    (B : Type*) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [IsLocalRing B] [IsNoetherianRing B]
    [Algebra (UVCrossingModel W (π ^ (m * n))) B] [Module.Finite (UVCrossingModel W (π ^ (m * n))) B]
    [FaithfulSMul (UVCrossingModel W (π ^ (m * n))) B]
    (K₀ : Type*) [Field K₀] [Algebra (UVCrossingModel W (π ^ (m * n))) K₀] [IsFractionRing (UVCrossingModel W (π ^ (m * n))) K₀]
    (F : Type*) [Field F] [Algebra K₀ F] [Algebra (UVCrossingModel W (π ^ (m * n))) F]
    [IsScalarTower (UVCrossingModel W (π ^ (m * n))) K₀ F]
    [Algebra B F] [IsScalarTower (UVCrossingModel W (π ^ (m * n))) B F] [IsFractionRing B F]
    [FiniteDimensional K₀ F] [IsGalois K₀ F] (hcyc : IsCyclic (F ≃ₐ[K₀] F)) (hdeg : Module.finrank K₀ F = n)
    (hunr : ∀ (𝔭 : Ideal B) [𝔭.IsPrime],
      (𝔭.comap (algebraMap (UVCrossingModel W (π ^ (m * n))) B)).height = 1 →
        Algebra.IsUnramifiedAt (UVCrossingModel W (π ^ (m * n))) 𝔭)
    (hres : ∀ b : B, ∃ w : W,
      b - algebraMap (UVCrossingModel W (π ^ (m * n))) B (const (π ^ (m * n)) w) ∈ IsLocalRing.maximalIdeal B) :
    ∃ e : B ≃+* UVCrossingModel W (π ^ m),
      ∀ w : W, e (algebraMap (UVCrossingModel W (π ^ (m * n))) B (const (π ^ (m * n)) w)) = const (π ^ m) w := by sorry
