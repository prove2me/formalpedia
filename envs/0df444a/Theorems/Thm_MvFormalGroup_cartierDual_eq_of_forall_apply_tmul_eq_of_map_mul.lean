-- Prove2me | Theorems.Thm_MvFormalGroup_cartierDual_eq_of_forall_apply_tmul_eq_of_map_mul
-- name    : MvFormalGroup.cartierDual_eq_of_forall_apply_tmul_eq_of_map_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/a710f02a-9a77-5dff-a8d4-2335bda3f3d0
-- title:
--   Uniqueness of a point derivation from its values on coordinates
-- statement:
--   Let $\mathcal{O}$ be a commutative ring, let $p$ be a natural number assumed prime, and fix an $\mathcal{O}$-algebra structure on $\mathbb{Z}/p$. Let $d$ be a natural number and let $R$ be a commutative ring carrying a Hopf algebra structure over $\mathcal{O}$ which is free and finite as an $\mathcal{O}$-module. Let $\pi : \mathcal{O}[[X_0,\dots,X_{d-1}]] \to R$ be a surjective homomorphism of $\mathcal{O}$-algebras from the ring of multivariate formal power series in the variables indexed by `Fin d`, and assume that for every $j$ the counit of the base-changed coalgebra $\mathbb{Z}/p \otimes_{\mathcal{O}} R$ over $\mathbb{Z}/p$ annihilates $1 \otimes \pi(X_j)$. Let $\delta, \delta'$ be elements of [`CartierDual (ZMod p) (ZMod p ⊗[𝓞] R)`](def/HopfAlgebra_CartierDual.html#L12), that is, $\mathbb{Z}/p$-linear functionals on $\mathbb{Z}/p \otimes_{\mathcal{O}} R$, each satisfying the counit-twisted Leibniz rule $\delta(ab) = \delta(a)\varepsilon(b) + \varepsilon(a)\delta(b)$ for all $a,b$, where $\varepsilon$ is that counit. If $\delta$ and $\delta'$ agree on $1 \otimes \pi(X_j)$ for every $j$, then $\delta = \delta'$.
--
--   This is the standard uniqueness statement for point derivations (derivations along the augmentation) on the special fibre of a finite flat Hopf algebra given by a power series presentation: such a functional is determined by its values on the images of the coordinates. It is used in the identification of the $p$-th convolution power of a point derivation in the Cartier dual with a combination of the coordinate derivations, in [`MvFormalGroup.exists_cartierDual_derivation_pow_eq_sum_hasseWitt_smul`](thm.html#MvFormalGroup.exists_cartierDual_derivation_pow_eq_sum_hasseWitt_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_cartierDual_eq_of_forall_apply_tmul_eq_of_map_mul.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct
open MvPowerSeries

universe u v

theorem MvFormalGroup.cartierDual_eq_of_forall_apply_tmul_eq_of_map_mul
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] [Algebra 𝓞 (ZMod p)]
    {d : ℕ} (R : Type v) [CommRing R] [HopfAlgebra 𝓞 R] [Module.Free 𝓞 R] [Module.Finite 𝓞 R]
    (π : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] R) (hπ : Function.Surjective π)
    (hε : ∀ j, Coalgebra.counit (R := ZMod p) ((1 : ZMod p) ⊗ₜ[𝓞] π (X j)) = 0)
    (δ δ' : CartierDual (ZMod p) (ZMod p ⊗[𝓞] R))
    (hδ : ∀ a b : ZMod p ⊗[𝓞] R, δ (a * b) =
      δ a * Coalgebra.counit (R := ZMod p) b + Coalgebra.counit (R := ZMod p) a * δ b)
    (hδ' : ∀ a b : ZMod p ⊗[𝓞] R, δ' (a * b) =
      δ' a * Coalgebra.counit (R := ZMod p) b + Coalgebra.counit (R := ZMod p) a * δ' b)
    (h : ∀ j, δ ((1 : ZMod p) ⊗ₜ[𝓞] π (X j)) = δ' ((1 : ZMod p) ⊗ₜ[𝓞] π (X j))) :
    δ = δ' := by sorry
