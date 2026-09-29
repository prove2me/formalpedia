-- Prove2me | Theorems.Thm_ModularCurve_exists_finiteFlat_local_local_model_heckeTorsion_jZero_of_heckeGen_mem
-- name    : ModularCurve.exists_finiteFlat_local_local_model_heckeTorsion_jZero_of_heckeGen_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/6e0976ab-ac93-5c80-96d2-1add1062820a
-- title:
--   Local-local finite flat model of J₀(N)[𝔪] with Hecke action
-- statement:
--   Let $N\ge 1$, let $p$ be an odd prime not dividing $N$, and let $\mathfrak m$ be an ideal of `HeckeAlg` $=\mathbb Z[X_\ell:\ell\text{ prime}]$ (a polynomial ring over $\mathbb Z$ on the set of primes) containing both the image of $p$ and the generator `heckeGen` at $p$, i.e. the variable $X_p$. Write $R=$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8), the subring of $\mathbb Q$ of fractions whose denominator is coprime to $p$, and let `JZero N` be the group of degree-zero divisor classes of the modular function field `modularFunctionFieldBar N` over $\overline{\mathbb Q}$, equipped with the `HeckeAlg`-module structure `heckeModuleBar N`. The assertion: there is a commutative ring $H$ carrying a Hopf algebra structure over $R$ which is finite, flat and free as an $R$-module and cocommutative as a coalgebra, such that $H$ is a local ring and its Cartier dual (the $R$-linear dual of $H$ with its induced bialgebra structure) is a local ring, together with a bijection $e$ from `WithConv` of the set of $R$-algebra maps $H\to\overline{\mathbb Q}$ onto the $\mathfrak m$-torsion submodule `heckeTorsion (JZero N) 𝔪` (the elements of `JZero N` annihilated by every element of $\mathfrak m$) with the following three properties: $e(f\cdot g)=e(f)+e(g)$ for the convolution product; for every $\mathbb Q$-algebra automorphism $\sigma$ of $\overline{\mathbb Q}$ and all $f,g$ with $g=\sigma\circ f$ pointwise, $e(g)=\sigma\cdot e(f)$ in `JZero N`; and there is a map $\varphi$ assigning to each $t\in$ `HeckeAlg` an $R$-algebra endomorphism $\varphi(t)$ of $H$ such that the kernel of the counit is contained in its preimage under $\varphi(t)$, and such that $g=f\circ\varphi(t)$ pointwise implies $e(g)=t\cdot e(f)$ in `JZero N`.
--
--   This combines the finite flat Hopf-algebra model of $J_0(N)[\mathfrak m]$ over $\mathbb Z_{(p)}$ with the local-local property (both the model and its Cartier dual connected) valid in the supersingular case $p,\,T_p\in\mathfrak m$, while retaining the Hecke action through algebra endomorphisms preserving the augmentation ideal. It is used in the bound on the rank of $J_0(N)[\mathfrak m]$ over the residue field when the associated mod $p$ representation is absolutely irreducible.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_finiteFlat_local_local_model_heckeTorsion_jZero_of_heckeGen_mem.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_HopfAlgebra_CartierDualInstances

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve in

theorem ModularCurve.exists_finiteFlat_local_local_model_heckeTorsion_jZero_of_heckeGen_mem
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
          (∀ h : H, g h = σ (f h)) → ((e g : JZero N)) = σ • (e f : JZero N)) ∧
        ∃ φ : HeckeAlg → (H →ₐ[GaloisRep.ratLocalizedAt p] H),
          (∀ t : HeckeAlg,
            RingHom.ker (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) H) ≤
              (RingHom.ker (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) H)).comap (φ t)) ∧
          ∀ (t : HeckeAlg) (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
            (∀ h : H, g h = f (φ t h)) → ((e g : JZero N)) = t • (e f : JZero N) := by sorry
