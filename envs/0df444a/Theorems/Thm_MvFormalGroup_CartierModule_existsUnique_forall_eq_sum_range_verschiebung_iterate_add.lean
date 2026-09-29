-- Prove2me | Theorems.Thm_MvFormalGroup_CartierModule_existsUnique_forall_eq_sum_range_verschiebung_iterate_add
-- name    : MvFormalGroup.CartierModule.existsUnique_forall_eq_sum_range_verschiebung_iterate_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/0d431d23-18f3-53a6-90c2-ce0f94fac6ba
-- title:
--   V-adic completeness of the Cartier module of a formal group
-- statement:
--   Let $p$ be a prime, $R$ a commutative ring of characteristic $p$, and $\Phi$ a $d$-dimensional formal group law over $R$ in the sense of [`MvFormalGroup`](def/MvFormalGroup_BasicV2.html#L15): a family of $d$ power series in the variables indexed by $\mathrm{Fin}\,d\sqcup\mathrm{Fin}\,d$ with vanishing constant coefficients, linear coefficients $\delta_{ij}$ in each block, and satisfying the associativity identity under substitution; assume $\Phi$ is commutative, i.e. each component is invariant under interchanging the two blocks of variables. Elements of [`MvFormalGroup.CartierModule p Φ`](def/MvFormalGroup_CartierModule.html#L162) are families of $d$ power series $f_j$ in variables indexed by $\mathbb{N}$, with vanishing constant coefficients, such that substituting the Witt addition family `WittLaw.addFam p R` (the images of the Witt addition polynomials $S_n$ in $R$) into $f_j$ agrees with substituting the two variable-shifted copies of $f$ into the $j$-th component of $\Phi$; this is an additive group. Write $V$ for [`MvFormalGroup.CartierModule.verschiebung`](def/MvFormalGroup_CartierModule.html#L628), the additive endomorphism obtained by substituting the family `WittLaw.frobFam` into each component. Given any sequence $(x_m)_{m\in\mathbb{N}}$ in this module, the assertion is that there is exactly one $s$ such that for every $N$ some $t$ satisfies $s=\sum_{m<N}V^m(x_m)+V^N t$.
--
--   This is the statement that the Cartier module $\mathrm{Hom}(\widehat W,\Phi)$ of a commutative formal group law in characteristic $p$ is separated and complete for the $V$-adic filtration, so that each formal series $\sum_m V^m x_m$ has a unique sum; the uniqueness part encodes $\bigcap_N V^N M=0$ and the existence part convergence of the partial sums. It underlies the basis and rank statements for Cartier modules used in the analysis of formal modules over quaternionic orders.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_CartierModule_existsUnique_forall_eq_sum_range_verschiebung_iterate_add.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem MvFormalGroup.CartierModule.existsUnique_forall_eq_sum_range_verschiebung_iterate_add
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p] {d : ℕ}
    (Φ : MvFormalGroup d R) [Φ.IsComm] (x : ℕ → MvFormalGroup.CartierModule p Φ) :
    ∃! s : MvFormalGroup.CartierModule p Φ, ∀ N : ℕ, ∃ t : MvFormalGroup.CartierModule p Φ,
      s = (∑ m ∈ Finset.range N,
              (⇑(MvFormalGroup.CartierModule.verschiebung (p := p) (Φ := Φ)))^[m] (x m)) +
            (⇑(MvFormalGroup.CartierModule.verschiebung (p := p) (Φ := Φ)))^[N] t := by sorry
