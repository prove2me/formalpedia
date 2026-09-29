-- Prove2me | Theorems.Thm_ModularCurve_exists_finiteFlat_local_local_model_jZero_torsion_heckeNilpotent
-- name    : ModularCurve.exists_finiteFlat_local_local_model_jZero_torsion_heckeNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/242994e6-f5ac-5616-b524-756881a6ed3f
-- title:
--   Local-local model of the Tₚ-nilpotent part of J₀(M)[p]
-- statement:
--   Let $M\ge 1$ be a natural number and let $p$ be a prime not dividing $M$. Write $R=\mathbb{Z}_{(p)}$ for the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of the rationals whose denominator is coprime to $p$. The assertion is that there exists a type $H$ carrying a commutative ring structure and the structure of a Hopf algebra over $R$ which is finite, flat and free as an $R$-module and cocommutative as a coalgebra, such that: $H$ is a local ring; the Cartier dual [`CartierDual R H`](def/HopfAlgebra_CartierDual.html#L12), namely the $R$-linear dual $H^{\vee}$ with its induced ring structure, is also a local ring; and there is a bijection $e$ from the set of $R$-algebra homomorphisms $H\to\overline{\mathbb{Q}}$, equipped with the convolution multiplication of `WithConv`, onto the submodule of `JZero M` — the degree-zero divisor class group $\mathrm{Pic}^0$ of the base change to $\overline{\mathbb{Q}}$ of the full modular function field of level $M$ — cut out by intersecting the $p$-torsion $\{x : px=0\}$ with the supremum over $m\in\mathbb{N}$ of the kernels of `heckeOperatorBar M p` raised to the power $m$; the bijection $e$ turns convolution into addition, $e(f\cdot g)=e(f)+e(g)$, and is Galois-equivariant in the following sense: for every $\sigma\in\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ and all points $f,g$, if $g(h)=\sigma(f(h))$ for every $h\in H$, then $e(g)=\sigma\cdot e(f)$ in `JZero M`.
--
--   This records, in Hopf-algebra form, that the part of $J_0(M)[p]$ annihilated by a power of $T_p$ at a prime $p$ of good reduction admits a finite flat model over $\mathbb{Z}_{(p)}$ whose associated group scheme is connected with connected Cartier dual (local-local), the Eichler–Shimura congruence $T_p=F+V$ on the special fibre excluding both the étale and the multiplicative parts. It supplies the local input for the construction of inertia eigenvectors with tame character attached to cusp forms, and is used in the derivation of the corresponding local-local model statement for Hecke torsion in $J_0(M)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_finiteFlat_local_local_model_jZero_torsion_heckeNilpotent.lean

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_HopfAlgebra_CartierDualInstances

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.exists_finiteFlat_local_local_model_jZero_torsion_heckeNilpotent
    (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact p.Prime] (hpM : ¬ p ∣ M) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H)
      (_ : Module.Finite (GaloisRep.ratLocalizedAt p) H)
      (_ : Module.Flat (GaloisRep.ratLocalizedAt p) H)
      (_ : Module.Free (GaloisRep.ratLocalizedAt p) H)
      (_ : Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H),
      IsLocalRing H ∧
      IsLocalRing (CartierDual (GaloisRep.ratLocalizedAt p) H) ∧
      ∃ e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
          ↥(Submodule.torsionBy ℤ (JZero M) (p : ℤ) ⊓
            ⨆ m : ℕ, LinearMap.ker (heckeOperatorBar M ⟨p, hp.out⟩ ^ m)),
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
          (∀ h : H, g h = σ (f h)) → ((e g : JZero M)) = σ • (e f : JZero M) := by sorry
