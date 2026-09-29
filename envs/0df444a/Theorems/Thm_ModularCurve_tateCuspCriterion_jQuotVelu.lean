-- Prove2me | Theorems.Thm_ModularCurve_tateCuspCriterion_jQuotVelu
-- name    : ModularCurve.tateCuspCriterion_jQuotVelu
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/e8d32c47-e752-5661-b641-4d8f731f290e
-- title:
--   Tate cusp criterion for the Vélu p-isogeny quotient
-- statement:
--   Fix a natural number $p$ with $p \neq 0$ (the `NeZero p` instance) and $p \neq 2$. The theorem asserts that the project's predicate [`ModularCurve.TateCuspCriterion p`](def/ModularCurve_MazurStepThreeInputs.html#L110) holds for the explicitly given function `jQuot`, which sends an integral Weierstrass model $W$ over $\mathbb{Z}$ and a point $Q$ of the base change $Wb$ of $W$ to $\overline{\mathbb{Q}}$ (the project's `AlgebraicClosure ℚ`) to $V.c_4^{3} / V.\Delta$, where $V$ is the Vélu quotient `Wb.veluQuotient` of $Wb$ along the finite set `Wb.oddOrderSummingSet Q (addOrderOf Q / 2)`, that is along the coordinate pairs of the multiples $Q, 2Q, \dots, \lfloor n/2 \rfloor Q$ for $n$ the additive order of $Q$; `veluQuotient S` is the model with the same $a_1, a_2, a_3$ and with $a_4$ and $a_6$ corrected by $-5\sum_P t_P$ and $-b_2\sum_P t_P - 7\sum_P w_P$ in the Vélu quantities $t = 6x^2 + b_2 x + b_4$, $u = g_y^2$, $w = u + xt$. Unfolding `TateCuspCriterion`, the content is: assume $p$ is prime; let $W$ be a Weierstrass curve over $\mathbb{Z}$ with $\Delta(W) \neq 0$; let $\ell$ be a prime with $\ell \neq p$, $\ell \mid \Delta(W)$ and $\ell \nmid c_4(W)$; let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $\ell$, in the sense that $\ell$ is a non-unit of $A$; and let $Q$ be a point of $Wb$ that is fixed by every $\mathbb{Q}$-automorphism of $\overline{\mathbb{Q}}$ and has additive order exactly $p$ (this Galois hypothesis is carried along but the conclusion is purely local). Then, writing $j(W) = c_4(W)^3/\Delta(W)$ for the image [`ModularCurve.jInt W`](def/ModularCurve_MazurStepThreeInputs.html#L88) in $\overline{\mathbb{Q}}$ and $|\cdot|$ for the multiplicative valuation attached to $A$: (i) $|j(W)| > 1$; (ii) if $Q$ lies in the zero component at $A$ — meaning, by the project's definition `InZeroComponentAt`, that $Q = 0$, or $Q = (x,y)$ with $x \notin A$, or $x, y \in A$ and the residues of $x, y$ give a nonsingular point of the reduction of $W$ over the residue field of $A$ — then $|jQuot(W,Q)| = |j(W)|^{p}$; (iii) if $Q$ does not lie in the zero component at $A$, then $|jQuot(W,Q)|^{p} = |j(W)|$.
--
--   This is the Tate-curve computation of the effect of a $p$-isogeny on the valuation of the $j$-invariant at a prime of multiplicative reduction: a kernel meeting the zero component (toric kernel) multiplies the valuation of the Tate parameter by $p$, a kernel meeting another component divides it by $p$, and $v(j) = -v(q)$. The formal statement differs from the textbook version in three ways: the quotient $j$-invariant is not taken abstractly but is the specific rational expression $c_4^3/\Delta$ of the Vélu model obtained from the summing set $\{Q, 2Q, \dots, \lfloor p/2 \rfloor Q\}$; the hypothesis $p \neq 2$ is needed for this particular term (for $p = 2$ the one-element summing set gives a different model); and the toric/non-toric dichotomy is expressed by the nonsingularity of the reduction of the coordinates of $Q$ modulo the maximal ideal of $A$. It supplies the cusp rule used in the verification of Mazur's Step 3 input at the Vélu $jQuot$, namely in [`WeierstrassCurve.mazurStepThree_not_inZeroComponentAt`](thm.html#WeierstrassCurve.mazurStepThree_not_inZeroComponentAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_tateCuspCriterion_jQuotVelu.lean

import Mathlib
import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine

theorem ModularCurve.tateCuspCriterion_jQuotVelu (p : ℕ) [NeZero p] (hp2 : p ≠ 2) :
    ModularCurve.TateCuspCriterion p
      (fun W Q =>
        let Wb := (W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)
        let V := Wb.veluQuotient (Wb.oddOrderSummingSet Q (addOrderOf Q / 2))
        (V.c₄ : AlgebraicClosure ℚ) ^ 3 / (V.Δ : AlgebraicClosure ℚ)) := by sorry
