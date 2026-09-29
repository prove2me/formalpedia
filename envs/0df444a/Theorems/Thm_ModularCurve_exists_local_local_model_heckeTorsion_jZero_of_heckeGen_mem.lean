-- Prove2me | Theorems.Thm_ModularCurve_exists_local_local_model_heckeTorsion_jZero_of_heckeGen_mem
-- name    : ModularCurve.exists_local_local_model_heckeTorsion_jZero_of_heckeGen_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/d3eb9d58-e76c-58ca-bd9d-314bbd2fa491
-- title:
--   Local-local ℤ₍ₚ₎-model of J₀(N)[𝔪], Hecke-free form
-- statement:
--   Let $N\ge 1$ and let $p$ be a prime with $p\neq 2$ and $p\nmid N$. Let $\mathfrak m$ be an ideal of `HeckeAlg`, the polynomial ring $\mathbb{Z}[X_\ell:\ell\text{ prime}]$ on indeterminates indexed by the primes, and assume that the image of the integer $p$ lies in $\mathfrak m$ and that the generator `heckeGen` attached to the prime $p$ (the indeterminate $X_p$, which acts as $T_p$) lies in $\mathfrak m$. Give `JZero N`, the group $\mathrm{Pic}^0$ of the modular function field of level $N$ over $\overline{\mathbb Q}$, its `HeckeAlg`-module structure `heckeModuleBar`, in which $X_\ell$ acts by the Hecke operator `heckeOperatorBar N ℓ`. Write $R=$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8), the subring of $\mathbb Q$ of rationals whose denominator is coprime to $p$. The assertion is that there exists a type $H$ carrying a commutative ring structure and a cocommutative Hopf algebra structure over $R$, finite, flat and free as an $R$-module, such that $H$ is a local ring, the Cartier dual [`CartierDual R H`](def/HopfAlgebra_CartierDual.html#L12) $=\operatorname{Hom}_R(H,R)$ is a local ring, and there is a bijection $e$ from `WithConv` of the set of $R$-algebra homomorphisms $H\to\overline{\mathbb Q}$ (that set with its convolution multiplication) onto the $\mathfrak m$-torsion `heckeTorsion (JZero N) 𝔪`, i.e. $\{x : m\cdot x=0\text{ for all }m\in\mathfrak m\}$, satisfying $e(f\ast g)=e(f)+e(g)$ and the following equivariance: for every $\mathbb Q$-algebra automorphism $\sigma$ of $\overline{\mathbb Q}$ and all $f,g$, if $g(h)=\sigma(f(h))$ for all $h\in H$ then $e(g)=\sigma\cdot e(f)$ in `JZero N`. No Hecke action on $H$ is asserted.
--
--   This is the locality half of the construction of a finite flat local-local $\mathbb{Z}_{(p)}$-group-scheme model for the $\mathfrak m$-torsion of the Jacobian at a maximal ideal containing $p$ and $T_p$, as in Mazur's analysis of the supersingular case; the two local conditions on $H$ and on its Cartier dual express that the corresponding finite flat group scheme and its dual are connected. It is used by the Hecke-equivariant refinement [`ModularCurve.exists_finiteFlat_local_local_model_heckeTorsion_jZero_of_heckeGen_mem`](thm.html#ModularCurve.exists_finiteFlat_local_local_model_heckeTorsion_jZero_of_heckeGen_mem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_local_local_model_heckeTorsion_jZero_of_heckeGen_mem.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_HopfAlgebra_CartierDualInstances

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve in

theorem ModularCurve.exists_local_local_model_heckeTorsion_jZero_of_heckeGen_mem
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpN : ¬ p ∣ N)
    (𝔪 : Ideal HeckeAlg) (hpm : ((p : ℕ) : HeckeAlg) ∈ 𝔪) (hss : heckeGen ⟨p, Fact.out⟩ ∈ 𝔪) :
    letI := heckeModuleBar N
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H)
      (_ : Module.Finite (GaloisRep.ratLocalizedAt p) H)
      (_ : Module.Flat (GaloisRep.ratLocalizedAt p) H)
      (_ : Module.Free (GaloisRep.ratLocalizedAt p) H)
      (_ : Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H),
      IsLocalRing H ∧
      IsLocalRing (CartierDual (GaloisRep.ratLocalizedAt p) H) ∧
      ∃ e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
          ↥(heckeTorsion (JZero N) 𝔪),
        (∀ f g, e (f * g) = e f + e g) ∧
        (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
          (∀ h : H, g h = σ (f h)) → ((e g : JZero N)) = σ • (e f : JZero N)) := by sorry
