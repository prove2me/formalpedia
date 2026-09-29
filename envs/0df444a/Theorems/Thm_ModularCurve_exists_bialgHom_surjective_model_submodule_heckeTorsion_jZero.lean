-- Prove2me | Theorems.Thm_ModularCurve_exists_bialgHom_surjective_model_submodule_heckeTorsion_jZero
-- name    : ModularCurve.exists_bialgHom_surjective_model_submodule_heckeTorsion_jZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/cedc8946-d07b-5603-8d3c-a614961f79f9
-- title:
--   Schematic closure of a Galois-stable subspace of J₀(N)[𝔪]
-- statement:
--   Fix $N\ge 1$, a prime $p$, and an ideal $\mathfrak m$ of $\mathbb T = \mathbb Z[T_\ell : \ell \text{ prime}]$ (realised as `HeckeAlg`, the polynomial ring over $\mathbb Z$ on the primes), and let $R =$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8), the subring of rationals whose denominator is coprime to $p$. Let $H$ be a commutative ring that is a cocommutative Hopf algebra over $R$, module-finite and flat over $R$. Write $J =$ `JZero N` for the degree-zero divisor class group $\mathrm{Pic}^0$ of the modular function field of level $N$ over $\overline{\mathbb Q}$, equipped with the $\mathbb T$-module structure `heckeModuleBar N`, and $J[\mathfrak m]$ for the submodule of elements annihilated by every element of $\mathfrak m$. Assume given: a bijection $e$ from the set of $R$-algebra homomorphisms $H \to \overline{\mathbb Q}$, carrying the convolution monoid structure, onto $J[\mathfrak m]$, which turns convolution into addition ($e(f\ast g) = e(f)+e(g)$) and is Galois-equivariant in the sense that whenever $g(h) = \sigma(f(h))$ for all $h \in H$ and $\sigma \in \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$, one has $e(g) = \sigma \cdot e(f)$ in $J$; a function $\varphi$ assigning to each $t \in \mathbb T$ an $R$-algebra endomorphism of $H$ (no additivity or multiplicativity in $t$ is assumed) such that $g(h) = f(\varphi(t)h)$ for all $h$ implies $e(g) = t \cdot e(f)$; the hypothesis that the Galois and $\mathbb T$ actions on $J$ commute; and a $\mathbb T/\mathfrak m$-submodule $V \subseteq J[\mathfrak m]$ stable under the Galois action `mTorsionGaloisRep` on $J[\mathfrak m]$. The conclusion asserts the existence of a commutative ring $H_V$ carrying a cocommutative Hopf algebra structure over $R$, module-finite and free over $R$, a surjective bialgebra homomorphism $\pi : H \to H_V$ over $R$, a bijection $e_V$ from the $R$-algebra homomorphisms $H_V \to \overline{\mathbb Q}$ onto $V$, and a family $\varphi_V(t)$ of $R$-algebra endomorphisms of $H_V$ indexed by $t \in \mathbb T$, such that $e_V(f)$, viewed in $J[\mathfrak m]$, equals $e(\pi \text{ followed by } f)$ for every $f$, and $\pi$ followed by $\varphi_V(t)$ equals $\varphi(t)$ followed by $\pi$ for every $t \in \mathbb T$.
--
--   This is the schematic closure of a Galois-stable Hecke-submodule $V$ of $J_0(N)[\mathfrak m]$ inside a finite flat model $\operatorname{Spec} H$: the quotient Hopf algebra $H_V$ is a finite free model over $\mathbb Z_{(p)}$ whose $\overline{\mathbb Q}$-points are exactly $V$, and the Hecke endomorphisms descend to it. It is used in the proof that $J_0(N)[\mathfrak m]$ has dimension at most $2$ over $\mathbb T/\mathfrak m$ when the associated residual representation is absolutely irreducible.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_bialgHom_surjective_model_submodule_heckeTorsion_jZero.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve in

theorem ModularCurve.exists_bialgHom_surjective_model_submodule_heckeTorsion_jZero
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] (𝔪 : Ideal HeckeAlg)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    (e : letI := heckeModuleBar N
      WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ ↥(heckeTorsion (JZero N) 𝔪))
    (he_add : letI := heckeModuleBar N
      ∀ f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), e (f * g) = e f + e g)
    (he_gal : letI := heckeModuleBar N
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
        (∀ h : H, g h = σ (f h)) →
          ((e g : ↥(heckeTorsion (JZero N) 𝔪)) : JZero N) = σ • ((e f : ↥(heckeTorsion (JZero N) 𝔪)) : JZero N))
    (φ : HeckeAlg → (H →ₐ[GaloisRep.ratLocalizedAt p] H))
    (hφ : letI := heckeModuleBar N
      ∀ (t : HeckeAlg) (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
        (∀ h : H, g h = f (φ t h)) → ((e g : ↥(heckeTorsion (JZero N) 𝔪)) : JZero N) = t • ((e f : ↥(heckeTorsion (JZero N) 𝔪)) : JZero N))
    (hsmc : letI := heckeModuleBar N
      SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg (JZero N))
    (V : letI := heckeModuleBar N; Submodule (HeckeAlg ⧸ 𝔪) ↥(heckeTorsion (JZero N) 𝔪))
    (hV : letI := heckeModuleBar N; haveI := hsmc
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : ↥(heckeTorsion (JZero N) 𝔪)),
        v ∈ V → mTorsionGaloisRep (JZero N) 𝔪 σ v ∈ V) :
    letI := heckeModuleBar N
    ∃ (HV : Type) (_ : CommRing HV) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) HV)
      (_ : Module.Finite (GaloisRep.ratLocalizedAt p) HV)
      (_ : Module.Free (GaloisRep.ratLocalizedAt p) HV)
      (_ : Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) HV)
      (π : H →ₐc[GaloisRep.ratLocalizedAt p] HV)
      (eV : WithConv (HV →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ ↥V)
      (φV : HeckeAlg → (HV →ₐ[GaloisRep.ratLocalizedAt p] HV)),
      Function.Surjective π ∧
      (∀ f : WithConv (HV →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        ((eV f : ↥V) : ↥(heckeTorsion (JZero N) 𝔪)) =
          e (WithConv.toConv
            ((WithConv.ofConv f).comp (π : H →ₐ[GaloisRep.ratLocalizedAt p] HV)))) ∧
      (∀ t : HeckeAlg,
        (φV t).comp (π : H →ₐ[GaloisRep.ratLocalizedAt p] HV) =
          (π : H →ₐ[GaloisRep.ratLocalizedAt p] HV).comp (φ t)) := by sorry
