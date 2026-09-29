-- Prove2me | Theorems.Thm_HopfAlgebra_exists_finiteFlat_padicInt_surjective_points_eq_of_galoisStable_addSubgroup
-- name    : HopfAlgebra.exists_finiteFlat_padicInt_surjective_points_eq_of_galoisStable_addSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/a56b47a3-64cb-554e-962a-f1848a549a24
-- title:
--   Finite flat quotient Hopf algebra with prescribed Galois-stable points
-- statement:
--   Fix a prime $p$ and write $\overline{\mathbb Q}_p$ for `PadicAlgCl p`, with $\Gamma = \overline{\mathbb Q}_p \simeq_{\mathbb Q_p} \overline{\mathbb Q}_p$ its group of $\mathbb Q_p$-algebra automorphisms. Let $G$ be a commutative ring carrying a Hopf algebra structure over $\mathbb Z_p$ that is finite and flat as a $\mathbb Z_p$-module and whose comultiplication is cocommutative. Let $M$ be an additive commutative group with a distributive action of $\Gamma$, and let $e$ be a bijection from `WithConv (G →ₐ[ℤ_[p]] PadicAlgCl p)`, the set of $\mathbb Z_p$-algebra homomorphisms $G \to \overline{\mathbb Q}_p$ with its convolution multiplication, onto $M$, such that $e(fg) = e(f) + e(g)$ for all $f,g$, and such that whenever $f, g$ satisfy $g(x) = \sigma(f(x))$ for all $x \in G$ one has $e(g) = \sigma \cdot e(f)$. Let $N \le M$ be an additive subgroup with $\sigma \cdot m \in N$ for all $\sigma \in \Gamma$ and $m \in N$. The conclusion asserts the existence of a commutative ring $H$ with a $\mathbb Z_p$-Hopf algebra structure, finite and flat as a $\mathbb Z_p$-module and cocommutative, together with a surjective $\mathbb Z_p$-bialgebra homomorphism $\varpi : G \to H$ such that: for every $\mathbb Z_p$-algebra homomorphism $h : H \to \overline{\mathbb Q}_p$ the element $e(h \circ \varpi)$ lies in $N$; every $m \in N$ equals $e(h \circ \varpi)$ for exactly one such $h$; and the assignment $h \mapsto e(h \circ \varpi)$ turns the convolution product of $H$-points into addition in $M$, i.e. $e((h h') \circ \varpi) = e(h \circ \varpi) + e(h' \circ \varpi)$.
--
--   In geometric language this produces, inside a finite flat commutative group scheme $\operatorname{Spec} G$ over $\mathbb Z_p$ whose $\overline{\mathbb Q}_p$-points are identified additively and $\Gamma$-equivariantly with $M$, a finite flat closed subgroup scheme $\operatorname{Spec} H$ whose $\overline{\mathbb Q}_p$-points are exactly the prescribed Galois-stable subgroup $N$ — the scheme-theoretic closure of the subgroup of the generic fibre cut out by $N$. It is used in the local analysis of flat deformation conditions, being cited by [`ResidualGaloisRep.isLocallyFlatCocycleAd_add`](thm.html#ResidualGaloisRep.isLocallyFlatCocycleAd_add).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_finiteFlat_padicInt_surjective_points_eq_of_galoisStable_addSubgroup.lean

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped PadicInt

theorem HopfAlgebra.exists_finiteFlat_padicInt_surjective_points_eq_of_galoisStable_addSubgroup
    (p : ℕ) [Fact p.Prime]
    (G : Type) [CommRing G] [HopfAlgebra ℤ_[p] G] [Module.Finite ℤ_[p] G] [Module.Flat ℤ_[p] G]
    [Coalgebra.IsCocomm ℤ_[p] G]
    {M : Type} [AddCommGroup M] [DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) M]
    (e : WithConv (G →ₐ[ℤ_[p]] PadicAlgCl p) ≃ M)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (f g : WithConv (G →ₐ[ℤ_[p]] PadicAlgCl p)),
      (∀ x : G, g x = σ (f x)) → e g = σ • (e f))
    (N : AddSubgroup M) (hN : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (m : M), m ∈ N → σ • m ∈ N) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
      ∃ (ϖ : G →ₐc[ℤ_[p]] H), Function.Surjective ϖ ∧
        (∀ h : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p),
          e (WithConv.toConv ((WithConv.ofConv h).comp (ϖ : G →ₐ[ℤ_[p]] H))) ∈ N) ∧
        (∀ m ∈ N, ∃! h : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p),
          e (WithConv.toConv ((WithConv.ofConv h).comp (ϖ : G →ₐ[ℤ_[p]] H))) = m) ∧
        (∀ h h' : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p),
          e (WithConv.toConv ((WithConv.ofConv (h * h')).comp (ϖ : G →ₐ[ℤ_[p]] H))) =
            e (WithConv.toConv ((WithConv.ofConv h).comp (ϖ : G →ₐ[ℤ_[p]] H))) +
              e (WithConv.toConv ((WithConv.ofConv h').comp (ϖ : G →ₐ[ℤ_[p]] H)))) := by sorry
