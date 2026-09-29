-- Prove2me | Theorems.Thm_MvFormalGroup_CartierModule_verschiebungInt_injective_and_tangent_surjective_and_ker_and_complete_of_algebra_padicInt
-- name    : MvFormalGroup.CartierModule.verschiebungInt_injective_and_tangent_surjective_and_ker_and_complete_of_algebra_padicInt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/58d44c44-c2fd-5ca1-8519-851889c898e0
-- title:
--   Cartier module over a ℤₚ-algebra is reduced
-- statement:
--   Let $p$ be a prime, let $R$ be a commutative ring carrying an algebra structure over the $p$-adic integers $\mathbb{Z}_p$, let $d$ be a natural number, and let $\Phi$ be a $d$-dimensional formal group law over $R$, i.e. a $d$-tuple of power series in the variables indexed by $\mathrm{Fin}\,d \oplus \mathrm{Fin}\,d$ with vanishing constant terms, identity linear parts in each block and the associativity identity, assumed commutative in the sense that interchanging the two blocks of variables fixes each component. Consider the Cartier module $M =$ `CartierModule p Φ`, whose elements are $d$-tuples of power series in variables indexed by $\mathbb{N}$, with vanishing constant terms, compatible with the universal Witt addition polynomials and the group law $\Phi$; the tangent map sends such a tuple to the family of coefficients of the first variable $X_0$ in each of its $d$ components, and `verschiebungInt` is the additive endomorphism $V$ of $M$ given by substituting the family `frobPolyFam`. Then four assertions hold: $V$ is injective; the tangent map $M \to R^d$ is surjective; for every $f \in M$, the tangent of $f$ vanishes if and only if $f$ lies in the image of $V$; and for every sequence $(x_m)_{m \in \mathbb{N}}$ in $M$ there is a unique $s \in M$ such that for every $N$ one has $s = \sum_{m < N} V^m(x_m) + V^N(t)$ for some $t \in M$.
--
--   This is the reducedness package for the Cartier module $\mathrm{Hom}(\widehat{W}, \Phi)$ of a commutative formal group law over a $\mathbb{Z}_p$-algebra: injectivity of the Verschiebung, surjectivity of the tangent map, the identification of its kernel with $VM$, and $V$-adic separatedness and completeness. It is used in the theory of formal $\mathcal{O}_D$-modules occurring in the Čerednik–Drinfeld uniformisation, for instance in the construction of homogeneous $V$-bases and in computations of tangent values over dual numbers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_CartierModule_verschiebungInt_injective_and_tangent_surjective_and_ker_and_complete_of_algebra_padicInt.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem MvFormalGroup.CartierModule.verschiebungInt_injective_and_tangent_surjective_and_ker_and_complete_of_algebra_padicInt
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R]
    [Algebra (PadicInt p) R]
    {d : ℕ} (Φ : MvFormalGroup d R) [Φ.IsComm] :
    Function.Injective
        (MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)) ∧
      Function.Surjective
        (MvFormalGroup.CartierModule.tangent : MvFormalGroup.CartierModule p Φ → Fin d → R) ∧
      (∀ f : MvFormalGroup.CartierModule p Φ,
        MvFormalGroup.CartierModule.tangent f = 0 ↔
          ∃ g : MvFormalGroup.CartierModule p Φ,
            MvFormalGroup.CartierModule.verschiebungInt g = f) ∧
      (∀ x : ℕ → MvFormalGroup.CartierModule p Φ,
        ∃! s : MvFormalGroup.CartierModule p Φ, ∀ N : ℕ, ∃ t : MvFormalGroup.CartierModule p Φ,
          s = (∑ m ∈ Finset.range N,
                (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[m] (x m)) +
              (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] t) := by sorry
