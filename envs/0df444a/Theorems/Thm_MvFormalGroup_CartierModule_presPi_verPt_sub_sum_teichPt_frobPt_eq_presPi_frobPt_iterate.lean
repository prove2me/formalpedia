-- Prove2me | Theorems.Thm_MvFormalGroup_CartierModule_presPi_verPt_sub_sum_teichPt_frobPt_eq_presPi_frobPt_iterate
-- name    : MvFormalGroup.CartierModule.presPi_verPt_sub_sum_teichPt_frobPt_eq_presPi_frobPt_iterate
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/86249a90-efb5-5e53-8fd8-be75e9049d53
-- title:
--   Cartier relation points lie in the kernel of Pi_f
-- statement:
--   Fix a prime $p$, a commutative ring $R$ of characteristic $p$, and a commutative formal group law $\Phi$ of dimension $d$ over $R$ (a $d$-tuple of power series in $\mathrm{Fin}\,d \oplus \mathrm{Fin}\,d$ variables with the unit, associativity and commutativity identities). Elements of [`MvFormalGroup.CartierModule p Φ`](def/MvFormalGroup_CartierModule.html#L162) are $d$-tuples of power series in variables indexed by $\mathbb{N}$ with vanishing constant term satisfying $f(S(X;Y)) = \Phi(f(X),f(Y))$ for the Witt addition polynomials; on them `frobenius`, `verschiebung` and `homothety a` act by precomposition with the Verschiebung, Frobenius and Teichmüller-multiplication endomorphisms of the Witt group law. Given $f : \mathrm{Fin}\,d \to$ this module, $N \in \mathbb{N}$, scalars $c_{m,i,l} \in R$ for $m < N$ and $i,l < d$, and $h : \mathrm{Fin}\,d \to$ this module with $F f_i = \sum_{m<N} V^m\bigl(\sum_l \langle c_{m,i,l}\rangle f_l\bigr) + V^N h_i$ for every $i$, the conclusion is: for every type $\tau$ and every $u : \mathrm{Fin}\,d \to$ `WittLaw.seriesPoint p R τ` (Witt vectors over $R[[\tau]]$ whose components have zero constant term and form a substitutable family), $$\Pi_f\Bigl(l \mapsto V_W u_l - \sum_i \sum_{m<N} [c_{m,i,l}]\,\mathrm{Frob}^m u_i\Bigr) = \Pi_h\bigl(i \mapsto \mathrm{Frob}^N u_i\bigr),$$ where $\Pi_g(w) = \sum_l (g_l)(w_l)$ is evaluation of a $d$-tuple of Cartier-module elements on a $d$-tuple of Witt series points.
--
--   This is the formal half of Cartier's presentation of a commutative formal group by Witt points: if the expansions of the $F f_i$ in terms of $V$, the Teichmüller homotheties and the $f_l$ are given to level $N$, then the corresponding relation points of $\widehat W^d$ are carried by $\Pi_f$ into the image of $\Pi_h$ composed with $\mathrm{Frob}^N$. It is used by [`MvFormalGroup.CartierModule.exists_forall_le_order_coeff_sub_of_forall_le_order_presPi`](thm.html#MvFormalGroup.CartierModule.exists_forall_le_order_coeff_sub_of_forall_le_order_presPi), the step that converts vanishing of $\Pi_f$ to a given order into a congruence for the point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_CartierModule_presPi_verPt_sub_sum_teichPt_frobPt_eq_presPi_frobPt_iterate.lean

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

theorem MvFormalGroup.CartierModule.presPi_verPt_sub_sum_teichPt_frobPt_eq_presPi_frobPt_iterate
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p] {d : ℕ}
    (Φ : MvFormalGroup d R) [Φ.IsComm]
    (f : Fin d → MvFormalGroup.CartierModule p Φ) (N : ℕ) (c : Fin N → Fin d → Fin d → R)
    (h : Fin d → MvFormalGroup.CartierModule p Φ)
    (hexp : ∀ i, MvFormalGroup.CartierModule.frobenius (f i) =
      (∑ m : Fin N, (⇑(MvFormalGroup.CartierModule.verschiebung (p := p) (Φ := Φ)))^[m]
          (∑ l : Fin d, MvFormalGroup.CartierModule.homothety (c m i l) (f l))) +
        (⇑(MvFormalGroup.CartierModule.verschiebung (p := p) (Φ := Φ)))^[N] (h i))
    {τ : Type v} (u : Fin d → MvFormalGroup.WittLaw.seriesPoint p R τ) :
    MvFormalGroup.CartierModule.presPi f
        (fun l => MvFormalGroup.WittLaw.verPt (u l) -
          ∑ i : Fin d, ∑ m : Fin N, MvFormalGroup.WittLaw.teichPt (c m i l)
            ((⇑(MvFormalGroup.WittLaw.frobPt (p := p) (R := R) (τ := τ)))^[m] (u i))) =
      MvFormalGroup.CartierModule.presPi h
        (fun i => (⇑(MvFormalGroup.WittLaw.frobPt (p := p) (R := R) (τ := τ)))^[N] (u i)) := by sorry
