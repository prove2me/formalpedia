-- Prove2me | Theorems.Thm_MvFormalGroup_CartierModule_existsUnique_addMonoidHom_apply_eq_of_frobenius_expansion
-- name    : MvFormalGroup.CartierModule.existsUnique_addMonoidHom_apply_eq_of_frobenius_expansion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/0d97ca6d-2785-5e75-b54a-20591a0f2093
-- title:
--   Cartier modules: maps determined by a V-basis
-- statement:
--   Let $p$ be a prime and $R$ a commutative ring equipped with a $\mathbb{Z}_p$-algebra structure, and let $\Phi$, $\Phi'$ be commutative formal group laws over $R$ in $d$ and $d'$ variables (so each is a tuple of power series with vanishing constant term, linear part the identity in each group of variables, associative, and commutative). Write $M$, $M'$ for their Cartier modules, whose elements are tuples of power series in the variables indexed by $\mathbb{N}$, with zero constant term, intertwining the Witt addition law with $\Phi$ (respectively $\Phi'$); these carry the additive operators $F$ (`frobenius`), $V$ (`verschiebungInt`) and the homotheties $\langle b\rangle$ (`homothety`), all obtained by substitution into the corresponding endomorphisms of the Witt law, and the tangent map sending an element to the family of coefficients of its linear terms. Let $\gamma_1,\dots,\gamma_d\in M$ be such that the matrix of their tangent vectors has unit determinant, let $\gamma'_1,\dots,\gamma'_d\in M'$ be arbitrary, and let $c_{m,i,k}\in R$ for $m\in\mathbb{N}$ and $i,k\in\{1,\dots,d\}$ be such that for every $i$ and every $N$ both $F\gamma_i$ and $F\gamma'_i$ equal $\sum_{m<N}V^m\bigl(\sum_k\langle c_{m,i,k}\rangle\gamma_k\bigr)$ plus an element of $V^NM$, respectively $\sum_{m<N}V^m\bigl(\sum_k\langle c_{m,i,k}\rangle\gamma'_k\bigr)$ plus an element of $V^NM'$. Then there is exactly one additive map $\theta\colon M\to M'$ with $\theta(\gamma_i)=\gamma'_i$ for all $i$, commuting with $V$, with every homothety $\langle b\rangle$ ($b\in R$), and with $F$.
--
--   This is the universal-property form of Cartier's presentation of the Cartier module of a formal group admitting a $V$-basis: an $F$-, $V$- and homothety-equivariant map out of $M$ may be prescribed freely on a $V$-basis provided the images satisfy the same $F$-expansion relations. It is used in the construction of maps between formal $\mathcal{O}_D$-modules in the Čerednik–Drinfeld part of the development, in particular to produce homomorphisms out of a module presented by structure constants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_CartierModule_existsUnique_addMonoidHom_apply_eq_of_frobenius_expansion.lean

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

theorem MvFormalGroup.CartierModule.existsUnique_addMonoidHom_apply_eq_of_frobenius_expansion
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [Algebra (PadicInt p) R]
    {d d' : ℕ} (Φ : MvFormalGroup d R) (Φ' : MvFormalGroup d' R) [Φ.IsComm] [Φ'.IsComm]
    (γ : Fin d → MvFormalGroup.CartierModule p Φ)
    (hγ : IsUnit (Matrix.of fun i j => MvFormalGroup.CartierModule.tangent (γ i) j).det)
    (γ' : Fin d → MvFormalGroup.CartierModule p Φ')
    (c : ℕ → Fin d → Fin d → R)
    (hF : ∀ (i : Fin d) (N : ℕ), ∃ h : MvFormalGroup.CartierModule p Φ,
      MvFormalGroup.CartierModule.frobenius (γ i) =
        (∑ m : Fin N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[(m : ℕ)]
          (∑ k : Fin d, MvFormalGroup.CartierModule.homothety (c m i k) (γ k))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] h)
    (hF' : ∀ (i : Fin d) (N : ℕ), ∃ h : MvFormalGroup.CartierModule p Φ',
      MvFormalGroup.CartierModule.frobenius (γ' i) =
        (∑ m : Fin N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ')))^[(m : ℕ)]
          (∑ k : Fin d, MvFormalGroup.CartierModule.homothety (c m i k) (γ' k))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ')))^[N] h) :
    ∃! θ : MvFormalGroup.CartierModule p Φ →+ MvFormalGroup.CartierModule p Φ',
      (∀ i, θ (γ i) = γ' i) ∧
      (∀ f, θ (MvFormalGroup.CartierModule.verschiebungInt f) =
        MvFormalGroup.CartierModule.verschiebungInt (θ f)) ∧
      (∀ (b : R) f, θ (MvFormalGroup.CartierModule.homothety b f) =
        MvFormalGroup.CartierModule.homothety b (θ f)) ∧
      (∀ f, θ (MvFormalGroup.CartierModule.frobenius f) =
        MvFormalGroup.CartierModule.frobenius (θ f)) := by sorry
