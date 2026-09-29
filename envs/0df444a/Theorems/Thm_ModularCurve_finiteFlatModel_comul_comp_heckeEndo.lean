-- Prove2me | Theorems.Thm_ModularCurve_finiteFlatModel_comul_comp_heckeEndo
-- name    : ModularCurve.finiteFlatModel_comul_comp_heckeEndo
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/01314333-e068-5802-8cc6-400f66a89383
-- title:
--   Hecke endomorphisms of a finite flat model are bialgebra maps
-- statement:
--   Fix $N \geq 1$, a prime $p$, and an ideal $\mathfrak m$ of $\mathbb{T} = \mathbb{Z}[X_\ell : \ell \text{ prime}]$ (the polynomial ring `HeckeAlg` on the primes). Let $R = \mathbb{Z}_{(p)}$ be the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of rationals whose denominator is coprime to $p$, and let $H$ be a commutative Hopf $R$-algebra that is finite and flat as an $R$-module. Write $J$ for `JZero N`, the group $\mathrm{Pic}^0$ of degree-zero divisor classes of the modular function field of level $N$ over $\overline{\mathbb Q}$, with its `heckeModuleBar N` module structure over $\mathbb{T}$, and $J[\mathfrak m]$ for the submodule of elements annihilated by every element of $\mathfrak m$. Assume given: a bijection $e$ from the type of $R$-algebra homomorphisms $H \to \overline{\mathbb Q}$, carrying the convolution multiplication induced by the Hopf structure, onto $J[\mathfrak m]$, satisfying $e(fg) = e(f) + e(g)$; a function $\varphi$ assigning to each $t \in \mathbb{T}$ an $R$-algebra endomorphism $\varphi(t)$ of $H$ (no compatibility with the ring structure of $\mathbb{T}$ is assumed); and the hypothesis that whenever $g = f \circ \varphi(t)$ pointwise on $H$, one has $e(g) = t \cdot e(f)$ in $J$. Then for every $t \in \mathbb{T}$, the comultiplication and counit of $H$ satisfy $\Delta \circ \varphi(t) = (\varphi(t) \otimes \varphi(t)) \circ \Delta$ and $\varepsilon \circ \varphi(t) = \varepsilon$ as $R$-linear maps.
--
--   This upgrades the Hecke action on a finite flat model of $J_0(N)[\mathfrak m]$ from algebra endomorphisms to bialgebra endomorphisms, i.e. to endomorphisms of the associated finite flat group scheme, so that constructions functorial in bialgebra maps (Dieudonné modules, primitives, cotangent spaces) may be applied. It is used in the bounding of $J_0(N)[\mathfrak m]$, in particular by [`ModularCurve.finrank_heckeTorsion_jZero_le_two_of_isAbsolutelyIrreducible_of_heckeGen_mem`](thm.html#ModularCurve.finrank_heckeTorsion_jZero_le_two_of_isAbsolutelyIrreducible_of_heckeGen_mem) and by the descriptions of the Cartier dual and of the primitives of the model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finiteFlatModel_comul_comp_heckeEndo.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve in
open scoped TensorProduct in

theorem ModularCurve.finiteFlatModel_comul_comp_heckeEndo
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] (𝔪 : Ideal HeckeAlg)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    (e : letI := heckeModuleBar N
      WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ ↥(heckeTorsion (JZero N) 𝔪))
    (he_add : letI := heckeModuleBar N
      ∀ f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), e (f * g) = e f + e g)
    (φ : HeckeAlg → (H →ₐ[GaloisRep.ratLocalizedAt p] H))
    (hφ : letI := heckeModuleBar N
      ∀ (t : HeckeAlg) (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
        (∀ h : H, g h = f (φ t h)) → ((e g : ↥(heckeTorsion (JZero N) 𝔪)) : JZero N) = t • ((e f : ↥(heckeTorsion (JZero N) 𝔪)) : JZero N))
    (t : HeckeAlg) :
    Coalgebra.comul (R := GaloisRep.ratLocalizedAt p) (A := H) ∘ₗ (φ t).toLinearMap =
        TensorProduct.map (φ t).toLinearMap (φ t).toLinearMap ∘ₗ
          Coalgebra.comul (R := GaloisRep.ratLocalizedAt p) (A := H) ∧
      Coalgebra.counit (R := GaloisRep.ratLocalizedAt p) (A := H) ∘ₗ (φ t).toLinearMap =
        Coalgebra.counit (R := GaloisRep.ratLocalizedAt p) (A := H) := by sorry
