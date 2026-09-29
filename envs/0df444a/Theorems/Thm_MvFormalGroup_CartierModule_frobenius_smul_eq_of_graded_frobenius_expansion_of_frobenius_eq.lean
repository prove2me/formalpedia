-- Prove2me | Theorems.Thm_MvFormalGroup_CartierModule_frobenius_smul_eq_of_graded_frobenius_expansion_of_frobenius_eq
-- name    : MvFormalGroup.CartierModule.frobenius_smul_eq_of_graded_frobenius_expansion_of_frobenius_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/5f0870d4-dfe2-5bb1-8905-57277400dbe9
-- title:
--   Twisting a graded F-expansion by Frobenius-exchanged Witt scalars
-- statement:
--   Let $p$ be a prime and $B$ a commutative ring, and let $\Phi$ be a $2$-dimensional formal group law over $B$ (a pair of power series in two families of $2$ variables, with zero constant term, linear coefficients given by the identity in each family, and associative) which is commutative, i.e. invariant under exchanging the two families of variables. Work in the additive group [`MvFormalGroup.CartierModule p Φ`](def/MvFormalGroup_CartierModule.html#L162) of pairs of power series in variables indexed by $\mathbb{N}$, with zero constant term, intertwining the Witt addition law with $\Phi$; on it, `frobenius`, `verschiebungInt` and `homothety a` ($a \in B$) are the additive endomorphisms given by substitution of the families `verFam`, `frobPolyFam` and `teichFam a`, and write $F$, $V$, $\langle a\rangle$ for them. Given $f : \mathrm{Fin}\,2 \to M$, scalars $c_{m,i,l} \in B$ for $m \in \mathbb{N}$ and $i,l \in \mathrm{Fin}\,2$ vanishing whenever $l \not\equiv m+i+1 \pmod 2$, remainders $h_{N,i} \in M$, and the hypothesis that for all $N$ and $i$
--   $$F f_i = \sum_{m<N} V^m\Bigl(\sum_{l} \langle c_{m,i,l}\rangle f_l\Bigr) + V^N h_{N,i},$$
--   and given $w_0,w_1 \in W(B)$ with $\sigma(w_i) = w_{i+1}$ for the Witt vector Frobenius $\sigma$ and indices in $\mathrm{Fin}\,2$, the conclusion is that for all $N \in \mathbb{N}$ and $i \in \mathrm{Fin}\,2$
--   $$F(w_i \cdot f_i) = \sum_{m<N} V^m\Bigl(\sum_{l} \langle c_{m,i,l}\rangle (w_l \cdot f_l)\Bigr) + V^N\bigl(\sigma^{N+1}(w_i) \cdot h_{N,i}\bigr).$$
--
--   The statement is the Cartier-module computation showing that a $\mathbb{Z}/2$-graded $F$-expansion of a pair of elements of the Cartier module of a $2$-dimensional commutative formal group is preserved, with the same structure constants, after twisting the two elements by Witt scalars exchanged by the Witt Frobenius. It is used by [`MvFormalGroup.CartierModule.exists_zp2Action_of_graded_frobenius_expansion`](thm.html#MvFormalGroup.CartierModule.exists_zp2Action_of_graded_frobenius_expansion), where such gradings are converted into an action of the unramified quadratic ring on the formal group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_CartierModule_frobenius_smul_eq_of_graded_frobenius_expansion_of_frobenius_eq.lean

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

theorem MvFormalGroup.CartierModule.frobenius_smul_eq_of_graded_frobenius_expansion_of_frobenius_eq
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B]
    (Φ : MvFormalGroup 2 B) [Φ.IsComm]
    (f : Fin 2 → MvFormalGroup.CartierModule p Φ)
    (c : ℕ → Fin 2 → Fin 2 → B)
    (hc : ∀ (m : ℕ) (i l : Fin 2), (l : ℕ) ≠ (m + i + 1) % 2 → c m i l = 0)
    (h : ℕ → Fin 2 → MvFormalGroup.CartierModule p Φ)
    (hexp : ∀ (N : ℕ) (i : Fin 2), MvFormalGroup.CartierModule.frobenius (f i) =
      (∑ m ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[m]
          (∑ l : Fin 2, MvFormalGroup.CartierModule.homothety (c m i l) (f l))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] (h N i))
    (w : Fin 2 → WittVector p B)
    (hw : ∀ i : Fin 2, WittVector.frobenius (w i) = w (i + 1)) :
    ∀ (N : ℕ) (i : Fin 2), MvFormalGroup.CartierModule.frobenius (w i • f i) =
      (∑ m ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[m]
          (∑ l : Fin 2, MvFormalGroup.CartierModule.homothety (c m i l) (w l • f l))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N]
          ((⇑(WittVector.frobenius (p := p) (R := B)))^[N + 1] (w i) • h N i) := by sorry
