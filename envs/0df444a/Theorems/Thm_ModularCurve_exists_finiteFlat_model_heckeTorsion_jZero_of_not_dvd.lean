-- Prove2me | Theorems.Thm_ModularCurve_exists_finiteFlat_model_heckeTorsion_jZero_of_not_dvd
-- name    : ModularCurve.exists_finiteFlat_model_heckeTorsion_jZero_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/cd768c04-2aa2-5fca-9fc7-0b2a6ccb8c2a
-- title:
--   Finite flat Hecke-equivariant model of J₀(N)[𝔪]
-- statement:
--   Let $N\ge 1$, let $p$ be a prime with $p\nmid N$, and let $\mathfrak m$ be an ideal of the Hecke algebra `HeckeAlg`, the polynomial ring $\mathbb Z[T_\ell:\ell\ \text{prime}]$, containing the image of $p$. Write $R=$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) for the subring of $\mathbb Q$ of rationals whose denominator is coprime to $p$, and let `JZero N` be the degree-zero divisor class group $\mathrm{Pic}^0$ of the modular function field of level $N$ base changed to $\overline{\mathbb Q}$, with its `HeckeAlg`-module structure `heckeModuleBar N` (evaluation of the indeterminate at $\ell$ at the operator `heckeOperatorBar N ℓ` when these commute, and the trivial evaluation otherwise). The assertion is that there exist a type $H$, a commutative ring structure on it and a Hopf algebra structure over $R$ such that $H$ is finite and flat as an $R$-module and its coalgebra is cocommutative, together with a bijection $e$ from `WithConv` of the set of $R$-algebra maps $H\to\overline{\mathbb Q}$ (that set with its convolution multiplication) onto the $\mathfrak m$-torsion `heckeTorsion (JZero N) 𝔪`, the submodule of elements annihilated by every element of $\mathfrak m$, with the properties: $e(f\cdot g)=e(f)+e(g)$; for every $\sigma\in\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ and all $f,g$ with $g(h)=\sigma(f(h))$ for all $h\in H$, one has $e(g)=\sigma\cdot e(f)$ in `JZero N`; and there is a map $\varphi$ assigning to each $t\in$ `HeckeAlg` an $R$-algebra endomorphism $\varphi_t$ of $H$ such that the kernel of the counit is contained in its preimage under $\varphi_t$, and such that for all $t$ and all $f,g$ with $g(h)=f(\varphi_t(h))$ for all $h\in H$, one has $e(g)=t\cdot e(f)$ in `JZero N`.
--
--   This provides a finite flat commutative cocommutative Hopf algebra over $\mathbb Z_{(p)}$ whose $\overline{\mathbb Q}$-points realise, Galois- and Hecke-equivariantly, the $\mathfrak m$-torsion of $J_0(N)$ for a prime $p\nmid N$ lying in $\mathfrak m$; classically this is the finite flat model obtained from the $p$-torsion of the Néron model, which is an abelian scheme over $\mathbb Z_{(p)}$ since $p\nmid N$. It is obtained here from the corresponding statement for the $p^k$-torsion together with the general descent of a finite flat model to a Galois- and operator-stable subgroup, and it feeds the construction of local-local models used in the level-lowering arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_finiteFlat_model_heckeTorsion_jZero_of_not_dvd.lean

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.exists_finiteFlat_model_heckeTorsion_jZero_of_not_dvd
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (𝔪 : Ideal HeckeAlg) (hpm : (p : HeckeAlg) ∈ 𝔪) :
    letI := heckeModuleBar N
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H),
      Module.Finite (GaloisRep.ratLocalizedAt p) H ∧ Module.Flat (GaloisRep.ratLocalizedAt p) H ∧
      Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H ∧
      ∃ e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
          ↥(heckeTorsion (JZero N) 𝔪),
        (∀ f g, e (f * g) = e f + e g) ∧
        (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
          (∀ h : H, g h = σ (f h)) → ((e g : JZero N)) = σ • (e f : JZero N)) ∧
        ∃ φ : HeckeAlg → (H →ₐ[GaloisRep.ratLocalizedAt p] H),
          (∀ t : HeckeAlg,
            RingHom.ker (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) H) ≤
              (RingHom.ker (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) H)).comap (φ t)) ∧
          ∀ (t : HeckeAlg) (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
            (∀ h : H, g h = f (φ t h)) → ((e g : JZero N)) = t • (e f : JZero N) := by sorry
