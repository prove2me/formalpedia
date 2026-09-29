-- Prove2me | Theorems.Thm_MvFormalGroup_CartierModule_varpiTuple_rel_and_sum_eq_of_rel
-- name    : MvFormalGroup.CartierModule.varpiTuple_rel_and_sum_eq_of_rel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/12397798-dd16-5e0d-83bb-76137596b329
-- title:
--   The varpi-relation passes to varpi f, and varpi g ≡ p f
-- statement:
--   Let $p$ be a prime, $B$ a commutative ring, and $a\colon\mathbb N\to(\mathrm{Fin}\,2\to B)$ a family of coefficients with $a_{0,0}a_{0,1}=p$ in $B$. Let $\Phi$ be a commutative formal group law of dimension $2$ over $B$ (a pair of power series in two groups of two variables, with vanishing constant terms, the normalised linear coefficients, associativity, and symmetry), and write $V$ for `verschiebungInt` on the Cartier module $\mathrm{CartierModule}\ p\ \Phi$ (whose elements are pairs of power series in variables indexed by $\mathbb N$ with zero constant term, compatible with the Witt addition law via $\Phi$), $\langle a\rangle$ for `homothety` $a$, and $[x]$ for the Teichmüller Witt vector of $x$ acting by scalars. Set $\pi(m,i)=(m+i+1)\bmod 2$. Let $f_0,f_1$ be elements of the Cartier module such that for all $N$ and $i$, modulo the image of $V^{N+1}$, $$p\cdot f_i=[p]\cdot f_i+\sum_{k<N}V^{k+1}\Bigl(\bigl(\textstyle\sum_{m<k+2}[a_{m,i}^{p^{k+1-m}}a_{k+1-m,\pi(m,i)}]\bigr)\cdot f_{\pi(k,i)}\Bigr),$$ and let $g_0,g_1$ together with remainders $r_{N,i}$ satisfy, for all $N$ and $i$, the exact identity $g_i=\sum_{m<N}V^m\langle a_{m,i}\rangle f_{\pi(m,i)}+V^N r_{N,i}$. Then, first, $g$ satisfies the same relation as $f$ displayed above, for every $N$ and $i$, modulo the image of $V^{N+1}$; and second, for every $N$ and $i$, $\sum_{m<N}V^m\langle a_{m,i}\rangle g_{\pi(m,i)}$ equals $p\cdot f_i$ modulo the image of $V^N$.
--
--   This is the Cartier-module form of the computation that, on the free module over the Cartier ring with $\varpi e_i=\sum_m V^m[a_{m,i}]e_{\pi(m,i)}$, one has $\varpi^2=[p]+\sum_{k\ge 1}V^k d_{k}$ and $\varpi$ commutes with $p-\varpi^2$, as in Boutot–Carayol's treatment of special formal $\mathcal O_D$-modules of dimension $2$. It is used in the construction of a homogeneous $V$-basis with prescribed structure constants for such modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_CartierModule_varpiTuple_rel_and_sum_eq_of_rel.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem MvFormalGroup.CartierModule.varpiTuple_rel_and_sum_eq_of_rel
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B]
    (a : ℕ → Fin 2 → B) (ha : a 0 0 * a 0 1 = (p : B))
    (Φ : MvFormalGroup 2 B) [Φ.IsComm]
    (f : Fin 2 → MvFormalGroup.CartierModule p Φ)
    (hrel : ∀ (N : ℕ) (i : Fin 2), ∃ s : MvFormalGroup.CartierModule p Φ,
      p • f i = WittVector.teichmuller p (p : B) • f i +
        (∑ k ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[k + 1]
          ((∑ m ∈ Finset.range (k + 2), WittVector.teichmuller p
              (a m i ^ p ^ (k + 1 - m) * a (k + 1 - m) (CerednikDrinfeld.FormalODModule.piIndex m i))) •
            f (CerednikDrinfeld.FormalODModule.piIndex k i))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N + 1] s)
    (g : Fin 2 → MvFormalGroup.CartierModule p Φ)
    (r : ℕ → Fin 2 → MvFormalGroup.CartierModule p Φ)
    (hg : ∀ (N : ℕ) (i : Fin 2), g i =
      (∑ m ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[m]
        (MvFormalGroup.CartierModule.homothety (a m i) (f (CerednikDrinfeld.FormalODModule.piIndex m i)))) +
      (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] (r N i)) :
    (∀ (N : ℕ) (i : Fin 2), ∃ s : MvFormalGroup.CartierModule p Φ,
      p • g i = WittVector.teichmuller p (p : B) • g i +
        (∑ k ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[k + 1]
          ((∑ m ∈ Finset.range (k + 2), WittVector.teichmuller p
              (a m i ^ p ^ (k + 1 - m) * a (k + 1 - m) (CerednikDrinfeld.FormalODModule.piIndex m i))) •
            g (CerednikDrinfeld.FormalODModule.piIndex k i))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N + 1] s) ∧
    (∀ (N : ℕ) (i : Fin 2), ∃ s : MvFormalGroup.CartierModule p Φ,
      (∑ m ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[m]
        (MvFormalGroup.CartierModule.homothety (a m i) (g (CerednikDrinfeld.FormalODModule.piIndex m i)))) +
      (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] s = p • f i) := by sorry
