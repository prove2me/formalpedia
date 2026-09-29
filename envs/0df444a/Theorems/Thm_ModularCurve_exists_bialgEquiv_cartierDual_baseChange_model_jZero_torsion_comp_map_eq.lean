-- Prove2me | Theorems.Thm_ModularCurve_exists_bialgEquiv_cartierDual_baseChange_model_jZero_torsion_comp_map_eq
-- name    : ModularCurve.exists_bialgEquiv_cartierDual_baseChange_model_jZero_torsion_comp_map_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/14eb641c-6afb-5008-8b0f-912694be71cc
-- title:
--   Hecke-equivariant Cartier self-duality of J₀(N)[p]
-- statement:
--   Fix $N\ge 1$ and a prime $p\neq 2$, and write $\mathbb{Z}_{(p)}$ for the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of the rationals whose denominator is coprime to $p$. Let $A$ be a commutative ring carrying a Hopf algebra structure over $\mathbb{Z}_{(p)}$ that is finite and flat as a module and whose comultiplication is cocommutative. Give $J_0(N) :=$ `JZero N`, the degree-zero divisor class group $\mathrm{Pic}^0$ of the base-changed modular function field of level $N$ over $\overline{\mathbb{Q}}$, the module structure `heckeModuleBar N` over `HeckeAlg` $= \mathbb{Z}[X_\ell : \ell \text{ prime}]$. The assertion is: for every bijection $e$ from the convolution monoid `WithConv` of $\mathbb{Z}_{(p)}$-algebra homomorphisms $A \to \overline{\mathbb{Q}}$ onto the submodule of elements of $J_0(N)$ killed by $p^1$, such that $e(fg) = e(f) + e(g)$, and such that whenever $g = \sigma \circ f$ pointwise for $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ one has $e(g) = \sigma \cdot e(f)$; for every assignment $\varphi$ of an algebra endomorphism $\varphi_t$ of $A$ to each $t \in$ `HeckeAlg` such that $g = f \circ \varphi_t$ pointwise implies $e(g) = t \cdot e(f)$; and for every assignment $\psi$ of a $\mathbb{Z}/p$-bialgebra endomorphism $\psi_t$ of $\mathbb{Z}/p \otimes_{\mathbb{Z}_{(p)}} A$ whose underlying algebra map is $\mathrm{id} \otimes \varphi_t$: there is an isomorphism of bialgebras $\theta$ from the Cartier dual [`CartierDual`](def/HopfAlgebra_CartierDual.html#L12) $(\mathbb{Z}/p$-linear dual) of $\mathbb{Z}/p \otimes_{\mathbb{Z}_{(p)}} A$ onto $\mathbb{Z}/p \otimes_{\mathbb{Z}_{(p)}} A$ satisfying $\theta \circ \psi_t^{D} = \psi_t \circ \theta$ for all $t$, where $\psi_t^{D} =$ [`CartierDual.map`](def/HopfAlgebra_CartierDualMap.html#L102) $(\psi_t)$ is the transpose.
--
--   This is the Hecke-equivariant auto-duality of the $p$-torsion of $J_0(N)$ for odd $p$, transported to a finite flat Hopf algebra model over $\mathbb{Z}_{(p)}$: the Fricke-twisted Weil pairing identifies the special fibre of the model with its Cartier dual compatibly with all Hecke operators. It feeds the comparison of the Dieudonné module of this finite flat group scheme, modulo the images of Verschiebung and of a Hecke operator, with Hecke torsion on the integral lattice side.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_bialgEquiv_cartierDual_baseChange_model_jZero_torsion_comp_map_eq.lean

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_HopfAlgebra_CartierDualMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
open scoped TensorProduct

theorem ModularCurve.exists_bialgEquiv_cartierDual_baseChange_model_jZero_torsion_comp_map_eq
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (A : Type) [CommRing A] [HopfAlgebra (GaloisRep.ratLocalizedAt p) A]
    [Module.Finite (GaloisRep.ratLocalizedAt p) A] [Module.Flat (GaloisRep.ratLocalizedAt p) A]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) A] :
    letI := heckeModuleBar N
    ∀ e : WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
        ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1)),
      (∀ f g : WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
          e (f * g) = e f + e g) →
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
          (∀ h : A, g h = σ (f h)) → ((e g : JZero N)) = σ • (e f : JZero N)) →
      ∀ φ : HeckeAlg → (A →ₐ[GaloisRep.ratLocalizedAt p] A),
        (∀ (t : HeckeAlg) (f g : WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
            (∀ h : A, g h = f (φ t h)) → ((e g : JZero N)) = t • (e f : JZero N)) →
      ∀ ψ : HeckeAlg →
          ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A →ₐc[ZMod p] (ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A),
        (∀ t : HeckeAlg,
            (ψ t : (ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A →ₐ[ZMod p]
                (ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A) =
              Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (φ t)) →
      ∃ θ : CartierDual (ZMod p) ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A) ≃ₐc[ZMod p]
          (ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A,
        ∀ t : HeckeAlg,
          (θ : CartierDual (ZMod p) ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A) →ₐc[ZMod p]
              (ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A).comp (CartierDual.map (ψ t)) =
            (ψ t).comp (θ : CartierDual (ZMod p) ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A) →ₐc[ZMod p]
              (ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A) := by sorry
