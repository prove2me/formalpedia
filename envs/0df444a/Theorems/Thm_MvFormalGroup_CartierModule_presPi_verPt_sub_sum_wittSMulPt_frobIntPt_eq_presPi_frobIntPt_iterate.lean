-- Prove2me | Theorems.Thm_MvFormalGroup_CartierModule_presPi_verPt_sub_sum_wittSMulPt_frobIntPt_eq_presPi_frobIntPt_iterate
-- name    : MvFormalGroup.CartierModule.presPi_verPt_sub_sum_wittSMulPt_frobIntPt_eq_presPi_frobIntPt_iterate
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/9a14324a-e71c-5d55-b23e-368972a6a261
-- title:
--   Presentation map kills Cartier relation points up to remainder
-- statement:
--   Fix a prime $p$, a commutative ring $R$, and a commutative $d$-dimensional formal group law $\Phi$ over $R$ (a $d$-tuple of power series in $\mathrm{Fin}\,d\oplus\mathrm{Fin}\,d$ variables with vanishing constant term, linear terms $X_i$ in each block, associative and symmetric). Let $f_1,\dots,f_d$ be elements of the Cartier module `CartierModule p Φ`, whose elements are $d$-tuples of power series in countably many variables with zero constant coefficient compatible with Witt addition and the group law $\Phi$. Let $N\in\mathbb N$, let $w_{m,i,l}\in W_p(R)$ for $m<N$ and $1\le i,l\le d$, and let $h_1,\dots,h_d$ again lie in the Cartier module, subject to the expansion hypothesis that for every $i$, $F f_i=\sum_{m<N}V^m\bigl(\sum_l w_{m,i,l}\cdot f_l\bigr)+V^N h_i$, where $F$ is `frobenius` (precomposition with the Verschiebung family) and $V$ is `verschiebungInt` (precomposition with the integral Frobenius family). Let $\tau$ be a type and $u_1,\dots,u_d$ points of the Witt group with coordinates in $\mathrm{MvPowerSeries}\,\tau\,R$ having zero constant coefficient and admitting substitution. Then the presentation map $\Pi_f(v)=\sum_l f_l(v_l)$, summed in $\Phi$, satisfies $\Pi_f\bigl(l\mapsto V u_l-\sum_i\sum_{m<N} w_{m,i,l}\cdot F^m u_i\bigr)=\Pi_h\bigl(i\mapsto F^N u_i\bigr)$, with $V$, $F$ and the $W_p(R)$-action here acting on Witt points.
--
--   This is the formal half of Cartier's second theorem — the computation of the relation points for the presentation $\hat W^d\to\Phi$ attached to a $V$-basis — in the form valid over an arbitrary base, with coefficients in $W_p(R)$ rather than Teichmüller representatives. It is a purely formal identity, with no hypothesis on $R$, and feeds the order estimate [`MvFormalGroup.CartierModule.exists_forall_le_order_coeff_sub_and_frobIntPt_iterate_of_forall_le_order_presPi`](thm.html#MvFormalGroup.CartierModule.exists_forall_le_order_coeff_sub_and_frobIntPt_iterate_of_forall_le_order_presPi).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_CartierModule_presPi_verPt_sub_sum_wittSMulPt_frobIntPt_eq_presPi_frobIntPt_iterate.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_WittPointFamily
import Definitions.Def_MvFormalGroup_WittPointFamilyInt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem MvFormalGroup.CartierModule.presPi_verPt_sub_sum_wittSMulPt_frobIntPt_eq_presPi_frobIntPt_iterate
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] {d : ℕ}
    (Φ : MvFormalGroup d R) [Φ.IsComm]
    (f : Fin d → MvFormalGroup.CartierModule p Φ) (N : ℕ)
    (w : Fin N → Fin d → Fin d → WittVector p R)
    (h : Fin d → MvFormalGroup.CartierModule p Φ)
    (hexp : ∀ i, MvFormalGroup.CartierModule.frobenius (f i) =
      (∑ m : Fin N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[(m : ℕ)]
          (∑ l : Fin d, w m i l • f l)) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] (h i))
    {τ : Type v} (u : Fin d → MvFormalGroup.WittLaw.seriesPoint p R τ) :
    MvFormalGroup.CartierModule.presPi f
        (fun l => MvFormalGroup.WittLaw.verPt (u l) -
          ∑ i : Fin d, ∑ m : Fin N, MvFormalGroup.WittLaw.wittSMulPt (w m i l)
            ((⇑(MvFormalGroup.WittLaw.frobIntPt (p := p) (R := R) (τ := τ)))^[(m : ℕ)] (u i))) =
      MvFormalGroup.CartierModule.presPi h
        (fun i => (⇑(MvFormalGroup.WittLaw.frobIntPt (p := p) (R := R) (τ := τ)))^[N] (u i)) := by sorry
