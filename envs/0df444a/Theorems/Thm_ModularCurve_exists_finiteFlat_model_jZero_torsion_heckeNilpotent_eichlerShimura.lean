-- Prove2me | Theorems.Thm_ModularCurve_exists_finiteFlat_model_jZero_torsion_heckeNilpotent_eichlerShimura
-- name    : ModularCurve.exists_finiteFlat_model_jZero_torsion_heckeNilpotent_eichlerShimura
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/ae9f2aee-3637-5d83-a57b-5c6e3d082e5b
-- title:
--   Eichler–Shimura congruence on a finite flat model of J₀(M)[p]
-- statement:
--   Let $M\ge 1$ be a natural number, let $p$ be a prime and assume $p\nmid M$. Write $R=\mathbb{Z}_{(p)}$ for the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of those rationals whose denominator is coprime to $p$, and $J =$ `JZero M`, the degree-zero divisor class group (degree-zero divisors modulo principal divisors) of the modular function field of level $M$ base changed to $\overline{\mathbb{Q}}$, carrying the action of $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ and the $\mathbb{Z}$-linear endomorphism $\bar T_p =$ `heckeOperatorBar M ⟨p, _⟩`. The assertion is that there exist a type $H$ with a commutative ring structure and a Hopf algebra structure over $R$ such that $H$ is finite and flat as an $R$-module and its comultiplication is cocommutative, together with a bijection $e$ from the type of $R$-algebra homomorphisms $H\to\overline{\mathbb{Q}}$ equipped with its convolution product (`WithConv`) onto the submodule $\operatorname{tors}_{\mathbb{Z}}(J,p)\sqcap\bigsqcup_{m}\ker(\bar T_p^{\,m})$ of $p$-torsion classes annihilated by some power of $\bar T_p$, and a bialgebra endomorphism $t$ of $H$, subject to: $e(f\ast g)=e(f)+e(g)$; for $\sigma\in\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ and points $f,g$ with $g(h)=\sigma(f(h))$ for all $h\in H$, $e(g)=\sigma\cdot e(f)$ in $J$; for points $f,g$ with $g(h)=f(t(h))$ for all $h$, $e(g)=\bar T_p(e(f))$ in $J$; for every $a\in H$, $p\mid t(a)^p-a^{p^2}$ in $H$; and for every $R$-linear form $\varphi:H\to R$, $p$ divides $(\varphi\circ t)^{p}-\varphi^{\,p^{2}}$ computed in the convolution ring on $\operatorname{Hom}_R(H,R)$.
--
--   This is the Eichler–Shimura congruence relation transported to a finite flat group scheme over $\mathbb{Z}_{(p)}$ prolonging the $\bar T_p$-nilpotent part of $J_0(M)[p]$: the last two clauses express $F\,t=F^2$ and $V\,t=V^2$ on the special fibre, in the respective forms of $p$-th power congruences in $H$ and in the dual convolution algebra. It is the form in which the result is used further on, in [`ModularCurve.exists_finiteFlat_local_local_model_jZero_torsion_heckeNilpotent`](thm.html#ModularCurve.exists_finiteFlat_local_local_model_jZero_torsion_heckeNilpotent); compared with the statement it is derived from, freeness of $H$ over $\mathbb{Z}_{(p)}$ is not recorded, and finiteness, flatness and cocommutativity appear as conjuncts rather than as instances.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_finiteFlat_model_jZero_torsion_heckeNilpotent_eichlerShimura.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.exists_finiteFlat_model_jZero_torsion_heckeNilpotent_eichlerShimura
    (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact p.Prime] (hpM : ¬ p ∣ M) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H),
      Module.Finite (GaloisRep.ratLocalizedAt p) H ∧ Module.Flat (GaloisRep.ratLocalizedAt p) H ∧
      Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H ∧
      ∃ (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
          ↥(Submodule.torsionBy ℤ (JZero M) (p : ℤ) ⊓
            ⨆ m : ℕ, LinearMap.ker (heckeOperatorBar M ⟨p, hp.out⟩ ^ m)))
        (t : H →ₐc[GaloisRep.ratLocalizedAt p] H),
        (∀ f g, e (f * g) = e f + e g) ∧
        (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
          (∀ h : H, g h = σ (f h)) → ((e g : JZero M)) = σ • (e f : JZero M)) ∧
        (∀ f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
          (∀ h : H, g h = f (t h)) →
            ((e g : JZero M)) = heckeOperatorBar M ⟨p, hp.out⟩ (e f : JZero M)) ∧
        (∀ a : H, (p : H) ∣ t a ^ p - a ^ (p ^ 2)) ∧
        (∀ φ : H →ₗ[GaloisRep.ratLocalizedAt p] GaloisRep.ratLocalizedAt p,
          (p : WithConv (H →ₗ[GaloisRep.ratLocalizedAt p] GaloisRep.ratLocalizedAt p)) ∣
            WithConv.toConv (φ ∘ₗ (t : H →ₗ[GaloisRep.ratLocalizedAt p] H)) ^ p -
              WithConv.toConv φ ^ (p ^ 2)) := by sorry
