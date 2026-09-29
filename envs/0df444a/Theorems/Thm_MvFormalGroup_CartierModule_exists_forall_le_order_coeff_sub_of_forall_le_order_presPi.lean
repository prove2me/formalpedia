-- Prove2me | Theorems.Thm_MvFormalGroup_CartierModule_exists_forall_le_order_coeff_sub_of_forall_le_order_presPi
-- name    : MvFormalGroup.CartierModule.exists_forall_le_order_coeff_sub_of_forall_le_order_presPi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/8ec429bd-51ee-5819-bb81-3e0d0d2b5130
-- title:
--   Approximate exactness of the Cartier presentation map
-- statement:
--   Let $p$ be a prime, $R$ a commutative ring of characteristic $p$, and $\Phi$ a commutative $d$-dimensional formal group law over $R$ (a $d$-tuple of power series in two families of $d$ variables, with vanishing constant terms, linear coefficients $\delta_{ij}$ in each family, and associative and commutative). Let $f_1,\dots,f_d$ be elements of the Cartier module $\mathrm{Hom}(\widehat W,\Phi)$, i.e. $d$-tuples of power series in variables indexed by $\mathbb N$ with zero constant term intertwining the Witt addition law with $\Phi$, whose tangent vectors (the coefficients of $X_0$ in each component) satisfy $\mathrm{tangent}(f_i)_j=\delta_{ij}$. Let $N\in\mathbb N$, $c_{m,i,l}\in R$ for $m<N$ and $i,l<d$, and $h_1,\dots,h_d$ in the Cartier module satisfy the structure equations $F f_i=\sum_{m<N}V^m\bigl(\sum_l \langle c_{m,i,l}\rangle f_l\bigr)+V^N h_i$, where $F$, $V$ and $\langle a\rangle$ are precomposition with the Verschiebung, Frobenius and Teichmüller families. Let $\tau$ be a finite type, $n\le p^N$, and let $w_1,\dots,w_d$ be Witt vectors over $\mathrm{MvPowerSeries}\,\tau\,R$ whose components have zero constant term and form a substitutable family, such that every component of $\Pi_f(w)=\sum_l f_l(w_l)$ has order at least $n$. Then there are such Witt points $u_1,\dots,u_d$ with, for all $l$ and every Witt index $k$, the $k$-th component of $w_l-\bigl(V_W u_l-\sum_i\sum_{m<N}[c_{m,i,l}]\,\mathrm{Frob}^m(u_i)\bigr)$ of order at least $n$.
--
--   This is the exactness half of Cartier's second theorem in presentation form: modulo power series of order $\ge n$ with $n\le p^N$, every tuple of Witt points killed by the map $(w_l)\mapsto\sum_l f_l(w_l)$ into $\Phi$ comes from the relation tuple attached to the structure equations with $N$ terms. It is used in the construction of homomorphisms out of $\Phi$ over perfect rings, in [`MvFormalGroup.CartierModule.exists_hom_map_eq_of_perfectRing`](thm.html#MvFormalGroup.CartierModule.exists_hom_map_eq_of_perfectRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_CartierModule_exists_forall_le_order_coeff_sub_of_forall_le_order_presPi.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_WittPointFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem MvFormalGroup.CartierModule.exists_forall_le_order_coeff_sub_of_forall_le_order_presPi
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p] {d : ℕ}
    (Φ : MvFormalGroup d R) [Φ.IsComm]
    (f : Fin d → MvFormalGroup.CartierModule p Φ)
    (hf : ∀ i j, MvFormalGroup.CartierModule.tangent (f i) j = if i = j then 1 else 0)
    (N : ℕ) (c : Fin N → Fin d → Fin d → R) (h : Fin d → MvFormalGroup.CartierModule p Φ)
    (hexp : ∀ i, MvFormalGroup.CartierModule.frobenius (f i) =
      (∑ m : Fin N, (⇑(MvFormalGroup.CartierModule.verschiebung (p := p) (Φ := Φ)))^[m]
          (∑ l : Fin d, MvFormalGroup.CartierModule.homothety (c m i l) (f l))) +
        (⇑(MvFormalGroup.CartierModule.verschiebung (p := p) (Φ := Φ)))^[N] (h i))
    {τ : Type v} [Finite τ] (n : ℕ) (hn : n ≤ p ^ N)
    (w : Fin d → MvFormalGroup.WittLaw.seriesPoint p R τ)
    (hw : ∀ j, (n : ℕ∞) ≤ ((MvFormalGroup.CartierModule.presPi f w).val j).order) :
    ∃ u : Fin d → MvFormalGroup.WittLaw.seriesPoint p R τ, ∀ (l : Fin d) (k : ℕ),
      (n : ℕ∞) ≤
        ((w l : WittVector p (MvPowerSeries τ R)).coeff k -
          ((MvFormalGroup.WittLaw.verPt (u l) -
              ∑ i : Fin d, ∑ m : Fin N, MvFormalGroup.WittLaw.teichPt (c m i l)
                ((⇑(MvFormalGroup.WittLaw.frobPt (p := p) (R := R) (τ := τ)))^[m] (u i)) :
              MvFormalGroup.WittLaw.seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)).coeff k).order := by sorry
