-- Prove2me | Theorems.Thm_ModularCurve_exists_finiteFlat_model_jZero_torsion_hecke_of_not_dvd
-- name    : ModularCurve.exists_finiteFlat_model_jZero_torsion_hecke_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/c1038b7c-c49e-50f4-a0bd-f9c94e11e6d3
-- title:
--   Finite flat Hopf model of J₀(N)[p^k] with Hecke action
-- statement:
--   Let $N\ge 1$, let $p$ be a prime with $p\nmid N$, and let $k\in\mathbb N$. Write $R=$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) for the subring of $\mathbb Q$ of rationals whose denominator is coprime to $p$, and let $J_0(N)(\overline{\mathbb Q})=$ `JZero N` be the group of degree-zero divisor classes of the modular function field of level $N$ over $\overline{\mathbb Q}$, equipped with the `HeckeAlg`-module structure `heckeModuleBar N`, where `HeckeAlg` $=\mathbb Z[X_\ell:\ell\ \text{prime}]$ acts through the Hecke operators `heckeOperatorBar N ℓ` when these commute (and through the zero evaluation otherwise). The assertion is that there exist a type $H$ with a commutative ring structure and a Hopf algebra structure over $R$ such that $H$ is finite and flat as an $R$-module, its comultiplication is cocommutative, and there is a bijection $e$ from `WithConv` of the set of $R$-algebra maps $H\to\overline{\mathbb Q}$ onto the submodule of elements of $J_0(N)(\overline{\mathbb Q})$ killed by $p^k$, with the following three properties: $e(f\cdot g)=e(f)+e(g)$ for the convolution product; for every $\mathbb Q$-algebra automorphism $\sigma$ of $\overline{\mathbb Q}$ and all $f,g$ with $g(h)=\sigma(f(h))$ for all $h\in H$, one has $e(g)=\sigma\cdot e(f)$; and there is a family $\varphi$ assigning to each $t\in$ `HeckeAlg` an $R$-algebra endomorphism $\varphi_t$ of $H$ which maps the kernel of the counit into itself (i.e. that kernel is contained in its preimage under $\varphi_t$), and such that for all $t$ and all $f,g$ with $g(h)=f(\varphi_t(h))$ for all $h\in H$, one has $e(g)=t\cdot e(f)$.
--
--   This is the statement that the $p^k$-torsion of $J_0(N)$ admits a finite flat model over $\mathbb Z_{(p)}$ for $p\nmid N$, in Hopf-algebra form and compatibly with the Galois and Hecke actions. It is used in the local analysis at $p$ of the torsion of $J_0(N)$, and is cited by [`ModularCurve.exists_finiteFlat_model_heckeTorsion_jZero_of_not_dvd`](thm.html#ModularCurve.exists_finiteFlat_model_heckeTorsion_jZero_of_not_dvd) and by [`ModularCurve.pow_finrank_primitives_baseChange_le_card_torsionBySet_intLattice_quotient`](thm.html#ModularCurve.pow_finrank_primitives_baseChange_le_card_torsionBySet_intLattice_quotient).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_finiteFlat_model_jZero_torsion_hecke_of_not_dvd.lean

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.exists_finiteFlat_model_jZero_torsion_hecke_of_not_dvd
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) (k : ℕ) :
    letI := heckeModuleBar N
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H),
      Module.Finite (GaloisRep.ratLocalizedAt p) H ∧ Module.Flat (GaloisRep.ratLocalizedAt p) H ∧
      Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H ∧
      ∃ e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
          ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ k)),
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
