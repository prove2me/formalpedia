-- Prove2me | Theorems.Thm_MvFormalGroup_CartierModule_exists_sum_verschiebungInt_iterate_smul_eq_sum_homothety_teichmuellerDigit_add
-- name    : MvFormalGroup.CartierModule.exists_sum_verschiebungInt_iterate_smul_eq_sum_homothety_teichmuellerDigit_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/a89ab1fa-8d13-5aad-a3a2-87761010818c
-- title:
--   Universal Teichmüller-digit normal form in Cartier modules
-- statement:
--   Let $p$ be a prime, $B$ a commutative ring and $\Phi$ a commutative formal group law of dimension $d$ over $B$ (a $d$-tuple of power series in two blocks of $d$ variables with vanishing constant term, identity linear part and the associativity identity, whose defining series are invariant under interchanging the two blocks). Let $M =$ [`MvFormalGroup.CartierModule p Φ`](def/MvFormalGroup_CartierModule.html#L162) be the associated Cartier module, whose elements are $d$-tuples of power series in countably many variables with vanishing constant term that transform the Witt addition laws into $\Phi$, and write $F$ for `frobenius` (precomposition with the Verschiebung family), $V$ for `verschiebungInt` (precomposition with the Frobenius-polynomial family) and $\langle a\rangle$ for `homothety a` (precomposition with the Teichmüller family of $a \in B$). Given $f : \mathrm{Fin}\,d \to M$, digits $c_{m,i,l} \in B$ and elements $h_{N,i} \in M$ such that for all $N$ and all $i$
--   $$F f_i = \sum_{m < N} V^m\Bigl(\sum_l \langle c_{m,i,l}\rangle f_l\Bigr) + V^N h_{N,i},$$
--   then for every $N \in \mathbb{N}$ and every family $S : \mathbb{N} \to \mathrm{Fin}\,d \to W(B)$ of Witt-vector coefficients there is $r \in M$ with
--   $$\sum_{m<N} V^m\Bigl(\sum_l S_{m,l}\cdot f_l\Bigr) = \sum_{n<N} V^n\Bigl(\sum_l \langle d_{n,l}\rangle f_l\Bigr) + V^N r,$$
--   where $\cdot$ is the action of $W(B)$ on $M$ and $d_{n,l}$ is the zeroth Witt coefficient of $(\mathrm{step}^n S)_{0,l}$ for the universal one-step operator $(\mathrm{step}\,T)_{m,l'} = T_{m+1,l'} + \sum_l \sigma^m\bigl(\mathrm{shift}_1(T_{0,l})\bigr)\cdot \tau(c_{m,l,l'})$, with $\sigma$ the Witt Frobenius, $\mathrm{shift}_1$ the shift of Witt components and $\tau$ the Teichmüller map.
--
--   This is the re-expansion procedure that puts an arbitrary $W(B)$-linear combination of the $V^m f_l$ into Teichmüller-digit normal form modulo $V^N M$, the digits being given by universal expressions in the Witt components of the coefficients and in the structure constants $c$; no uniqueness of $V$-expansions and no reducedness of the Cartier module enters. It is used in the Čerednik–Drinfel'd part of the development, by [`CerednikDrinfeld.CartierLift.exists_digits_forall_smul_eq_teichmuller_smul_add_sum_verschiebungInt`](thm.html#CerednikDrinfeld.CartierLift.exists_digits_forall_smul_eq_teichmuller_smul_add_sum_verschiebungInt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_CartierModule_exists_sum_verschiebungInt_iterate_smul_eq_sum_homothety_teichmuellerDigit_add.lean

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

theorem MvFormalGroup.CartierModule.exists_sum_verschiebungInt_iterate_smul_eq_sum_homothety_teichmuellerDigit_add
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] {d : ℕ}
    (Φ : MvFormalGroup d B) [Φ.IsComm]
    (f : Fin d → MvFormalGroup.CartierModule p Φ)
    (c : ℕ → Fin d → Fin d → B)
    (h : ℕ → Fin d → MvFormalGroup.CartierModule p Φ)
    (hexp : ∀ (N : ℕ) (i : Fin d), MvFormalGroup.CartierModule.frobenius (f i) =
      (∑ m ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[m]
          (∑ l : Fin d, MvFormalGroup.CartierModule.homothety (c m i l) (f l))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] (h N i))
    (N : ℕ) (S : ℕ → Fin d → WittVector p B) :
    ∃ r : MvFormalGroup.CartierModule p Φ,
      (∑ m ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[m]
          (∑ l : Fin d, S m l • f l)) =
      (∑ n ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[n]
          (∑ l : Fin d, MvFormalGroup.CartierModule.homothety
            ((((fun T : ℕ → Fin d → WittVector p B => fun (m : ℕ) (l' : Fin d) =>
                  T (m + 1) l' + ∑ l : Fin d,
                    (⇑(WittVector.frobenius (p := p) (R := B)))^[m] ((T 0 l).shift 1) *
                      WittVector.teichmuller p (c m l l'))^[n] S) 0 l).coeff 0) (f l))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] r := by sorry
