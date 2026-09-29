-- Prove2me | Theorems.Thm_MvFormalGroup_CartierModule_existsUnique_forall_eq_sum_range_verschiebungInt_iterate_add
-- name    : MvFormalGroup.CartierModule.existsUnique_forall_eq_sum_range_verschiebungInt_iterate_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/63b41e12-27f0-5fb1-b3d8-f18ef094f487
-- title:
--   V-adic completeness and separatedness of the Cartier module
-- statement:
--   Let $p$ be a prime, $R$ a commutative ring, $d$ a natural number and $\Phi$ a $d$-dimensional formal group law over $R$, i.e. a $d$-tuple of power series in two families of $d$ variables with zero constant terms, linear coefficients the identity in each group of variables, and satisfying associativity; assume $\Phi$ is commutative in the sense of [`MvFormalGroup.IsComm`](def/MvFormalGroup_BasicV2.html#L52), that the substitution interchanging the two families of variables fixes each component of $\Phi$. Let $M =$ [`MvFormalGroup.CartierModule p Φ`](def/MvFormalGroup_CartierModule.html#L162) be the group of $d$-tuples $f$ of power series in variables indexed by $\mathbb{N}$ over $R$ with zero constant coefficients such that substituting the Witt addition family `WittLaw.addFam p R` into $f$ agrees with substituting the two variable-disjoint copies of $f$ into $\Phi$, and let $V =$ [`MvFormalGroup.CartierModule.verschiebungInt`](def/MvFormalGroup_CartierModuleIntVerschiebung.html#L318) be the additive endomorphism of $M$ obtained by precomposition with the endomorphism family `WittLaw.frobPolyFam` of the Witt group law. Then for every sequence $x : \mathbb{N} \to M$ there is exactly one $s \in M$ such that for each $N$ there exists $t \in M$ with $s = \sum_{m < N} V^m(x_m) + V^N t$.
--
--   This is the completeness and separatedness of the Cartier module $\mathrm{Hom}(\widehat{W},\Phi)$ for the $V$-adic filtration over an arbitrary base ring, which is what gives meaning to infinite expansions $\sum_m V^m x_m$ and is one of the axioms for a reduced Cartier module. It underlies the computations with Verschiebung and Teichmüller expansions in the formal $\mathcal{O}_D$-module theory used in the Čerednik–Drinfeld setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_CartierModule_existsUnique_forall_eq_sum_range_verschiebungInt_iterate_add.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem MvFormalGroup.CartierModule.existsUnique_forall_eq_sum_range_verschiebungInt_iterate_add
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] {d : ℕ}
    (Φ : MvFormalGroup d R) [Φ.IsComm] (x : ℕ → MvFormalGroup.CartierModule p Φ) :
    ∃! s : MvFormalGroup.CartierModule p Φ, ∀ N : ℕ, ∃ t : MvFormalGroup.CartierModule p Φ,
      s = (∑ m ∈ Finset.range N,
              (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[m] (x m)) +
            (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] t := by sorry
