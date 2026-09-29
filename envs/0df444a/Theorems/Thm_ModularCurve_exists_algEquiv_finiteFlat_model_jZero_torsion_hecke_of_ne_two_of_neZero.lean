-- Prove2me | Theorems.Thm_ModularCurve_exists_algEquiv_finiteFlat_model_jZero_torsion_hecke_of_ne_two_of_neZero
-- name    : ModularCurve.exists_algEquiv_finiteFlat_model_jZero_torsion_hecke_of_ne_two_of_neZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/e88a1666-a0a8-5208-832f-74c397be9f80
-- title:
--   Uniqueness of finite flat Hopf models of J₀(N)[p] with Hecke action
-- statement:
--   Let $N \ge 1$, let $p$ be a prime with $p \neq 2$, and write $R = \mathbf{Z}_{(p)}$ for the subring of $\mathbf{Q}$ consisting of those rationals whose denominator is coprime to $p$. Let $J$ denote `JZero N`, the group of degree-zero divisor classes (degree-zero divisors modulo principal divisors) of the modular function field of level $N$ over $\overline{\mathbf{Q}}$, with its action of $\mathrm{Gal}(\overline{\mathbf{Q}}/\mathbf{Q})$ and, through `heckeModuleBar N`, of the Hecke algebra $\mathbf{T} = \mathbf{Z}[X_\ell : \ell \text{ prime}]$; let $J[p]$ be the submodule of elements killed by $p^1$. Suppose given two commutative Hopf $R$-algebras $H$ and $H_0$, each finite and flat as an $R$-module, each with a bijection $e$ (resp. $e_0$) from the set $\mathrm{Hom}_{R\text{-alg}}(H,\overline{\mathbf{Q}})$, taken with its convolution multiplication, onto $J[p]$ which is additive, $e(f*g) = e(f)+e(g)$, and Galois-equivariant in the sense that $g = \sigma \circ f$ pointwise implies $e(g) = \sigma \cdot e(f)$ in $J$; and suppose given for each $t \in \mathbf{T}$ an $R$-algebra endomorphism $\varphi_t$ of $H$ (resp. $\varphi_{0,t}$ of $H_0$), not assumed to depend on $t$ in any ring-theoretic way, such that the kernel of the counit is contained in its preimage under $\varphi_t$ and such that $g = f \circ \varphi_t$ pointwise implies $e(g) = t \cdot e(f)$ (and likewise for $H_0$, $e_0$, $\varphi_{0,t}$). Then there exists an $R$-algebra isomorphism $\iota \colon H_0 \xrightarrow{\sim} H$ with $\varepsilon_H \circ \iota = \varepsilon_{H_0}$, with $e_0(f \circ \iota) = e(f)$ for every $f \in \mathrm{Hom}_{R\text{-alg}}(H,\overline{\mathbf{Q}})$, and with $\iota \circ \varphi_{0,t} = \varphi_t \circ \iota$ for every $t \in \mathbf{T}$.
--
--   This is Raynaud's uniqueness of finite flat prolongations of a finite group scheme over a discrete valuation ring of absolute ramification index $1 < p-1$, in the shape required here: two finite flat Hopf models over $\mathbf{Z}_{(p)}$ of the Galois module $J_0(N)[p]$, each compatible with the Hecke endomorphisms, are isomorphic compatibly with augmentation, points and Hecke action. It is used to transfer the Hecke action to the cotangent space of such a model, in [`ModularCurve.exists_linearEquiv_baseChange_cotangent_model_jZero_torsion_tensor_intLattice_comp_mapCotangent_eq`](thm.html#ModularCurve.exists_linearEquiv_baseChange_cotangent_model_jZero_torsion_tensor_intLattice_comp_mapCotangent_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_algEquiv_finiteFlat_model_jZero_torsion_hecke_of_ne_two_of_neZero.lean

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

set_option autoImplicit false

theorem ModularCurve.exists_algEquiv_finiteFlat_model_jZero_torsion_hecke_of_ne_two_of_neZero
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
      ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1)))
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ h : H, g h = σ (f h)) → ((e g : JZero N)) = σ • (e f : JZero N))
    (φ : HeckeAlg → (H →ₐ[GaloisRep.ratLocalizedAt p] H))
    (hφI : ∀ t : HeckeAlg,
      RingHom.ker (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) H) ≤
        (RingHom.ker (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) H)).comap (φ t))
    (hφ : letI := heckeModuleBar N
      ∀ (t : HeckeAlg) (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ h : H, g h = f (φ t h)) → ((e g : JZero N)) = t • (e f : JZero N))
    (H₀ : Type) [CommRing H₀] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H₀]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H₀] [Module.Flat (GaloisRep.ratLocalizedAt p) H₀]
    (e₀ : WithConv (H₀ →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
      ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1)))
    (he₀_add : ∀ f g, e₀ (f * g) = e₀ f + e₀ g)
    (he₀_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H₀ →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ h : H₀, g h = σ (f h)) → ((e₀ g : JZero N)) = σ • (e₀ f : JZero N))
    (φ₀ : HeckeAlg → (H₀ →ₐ[GaloisRep.ratLocalizedAt p] H₀))
    (hφ₀I : ∀ t : HeckeAlg,
      RingHom.ker (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) H₀) ≤
        (RingHom.ker (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) H₀)).comap (φ₀ t))
    (hφ₀ : letI := heckeModuleBar N
      ∀ (t : HeckeAlg) (f g : WithConv (H₀ →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ h : H₀, g h = f (φ₀ t h)) → ((e₀ g : JZero N)) = t • (e₀ f : JZero N)) :
    ∃ ι : H₀ ≃ₐ[GaloisRep.ratLocalizedAt p] H,
      (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) H).comp ι.toAlgHom =
        Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) H₀ ∧
      (∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        e₀ (WithConv.toConv (f.ofConv.comp ι.toAlgHom)) = e f) ∧
      ∀ t : HeckeAlg, ι.toAlgHom.comp (φ₀ t) = (φ t).comp ι.toAlgHom := by sorry
