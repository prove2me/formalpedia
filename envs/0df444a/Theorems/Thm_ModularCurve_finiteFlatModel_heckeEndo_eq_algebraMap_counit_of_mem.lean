-- Prove2me | Theorems.Thm_ModularCurve_finiteFlatModel_heckeEndo_eq_algebraMap_counit_of_mem
-- name    : ModularCurve.finiteFlatModel_heckeEndo_eq_algebraMap_counit_of_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/9e003fab-c58d-57e4-9020-2ae2b5ba52cc
-- title:
--   Elements of 𝔪 act trivially on a finite flat model
-- statement:
--   Fix a natural number $N \ne 0$, a prime $p$, and an ideal $\mathfrak m$ of the Hecke polynomial ring `HeckeAlg` $= \mathbb Z[X_\ell : \ell \text{ prime}]$, and let $H$ be a commutative Hopf algebra over the subring $R =$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb Q$ consisting of the rationals whose denominator is coprime to $p$, with $H$ finite and flat as an $R$-module. Write $J =$ `JZero N` for the group of degree-zero divisor classes of the modular function field of level $N$ base-changed to $\overline{\mathbb Q}$, equipped with the `HeckeAlg`-module structure `heckeModuleBar N`, and let `heckeTorsion (JZero N) 𝔪` be the submodule of elements annihilated by every element of $\mathfrak m$. Assume given: a bijection $e$ from the type of $R$-algebra homomorphisms $H \to \overline{\mathbb Q}$, carrying its convolution monoid structure via `WithConv`, onto that torsion submodule; the hypothesis that $e$ takes convolution products to sums, $e(f \ast g) = e(f) + e(g)$; a function $\varphi$ assigning to each element $t$ of `HeckeAlg` an $R$-algebra endomorphism $\varphi(t)$ of $H$; and the compatibility that whenever $g = f \circ \varphi(t)$ pointwise, one has $e(g) = t \cdot e(f)$ in $J$. Then for every $t \in \mathfrak m$ and every $h \in H$, $\varphi(t)(h)$ equals the image under the structure map $R \to H$ of the counit $\varepsilon(h)$.
--
--   This is the linearisation step for a finite flat model $H$ over $\mathbb Z_{(p)}$ of the $\mathfrak m$-torsion of $J_0(N)$: on such a model every element of $\mathfrak m$ acts through the trivial endomorphism $\eta \circ \varepsilon$, so that the Hecke action on $H$ factors through the quotient by $\mathfrak m$. It is used in bounding the rank of the $\mathfrak m$-torsion, in [`ModularCurve.finrank_heckeTorsion_jZero_le_two_of_isAbsolutelyIrreducible_of_heckeGen_mem`](thm.html#ModularCurve.finrank_heckeTorsion_jZero_le_two_of_isAbsolutelyIrreducible_of_heckeGen_mem) and in [`ModularCurve.pow_finrank_primitives_baseChange_le_card_torsionBySet_intLattice_quotient`](thm.html#ModularCurve.pow_finrank_primitives_baseChange_le_card_torsionBySet_intLattice_quotient).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finiteFlatModel_heckeEndo_eq_algebraMap_counit_of_mem.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve in

theorem ModularCurve.finiteFlatModel_heckeEndo_eq_algebraMap_counit_of_mem
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
    (t : HeckeAlg) (ht : t ∈ 𝔪) (h : H) :
    φ t h = algebraMap (GaloisRep.ratLocalizedAt p) H (Coalgebra.counit h) := by sorry
