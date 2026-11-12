-- Prove2me | Theorems.Thm_HolonomicPositivity_Robust_lemma_5_3
-- name    : HolonomicPositivity.Robust.lemma_5_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:31:22.724687+00:00
-- url     : https://prove2.me/theorems/838eec5d-91d8-4e8a-90c4-1b64b400bae1
-- title:
--   Lemma 5.3 — rational witness characterization of inequality (6)
-- statement:
--   Let $A,B\in\mathbb R(x)$ with $B>0$, that is, $B(x)>0$ for all sufficiently large real $x$. Then
--
--   $$\frac{A(x)}{B(x)B(x-1)}\ge-\frac14-\frac1{16x^2}+O(x^{-3})$$
--
--   holds if and only if there is $L\in\mathbb R(x)$ such that, in the eventual order as $x\to+\infty$,
--
--   1. $0<L(x+1)<B(x)$;
--   2. $L(x)(B(x)-L(x+1))+A(x)\ge0$.
--
--   This characterizes the second-order threshold (6), which corresponds to the convergence condition for continued fractions, by the existence of a rational witness. Here $A$ and $B$ play the roles of canonical numerators and denominators of continued fractions.
--
--   Differences from the source:
--   - encoding: the rational function $\frac{A(x)}{B(x)B(x-1)}$ and the shifts $L(x+1),B(x-1)$ in $\mathbb R(x)$ → the corresponding real functions built by evaluating $A,B,L$ at shifted real points; reason: these agree with the rational functions except at finitely many poles, and every relation they enter is eventual.
-- source:
--   Fugen Hagihara, STOC 2027 submission #328 (October 2026), Lemma 5.3, PDF p.10 (printed XX:10); inequality (6), PDF p.5.

import Mathlib
import Definitions.Def_HolonomicPositivity_Robust_Conditions

namespace HolonomicPositivity.Robust

/-- Lemma 5.3, PDF p.10 (XX:10). -/
theorem lemma_5_3 (A B : RatFunc ℝ) (hB : EventuallyGT (ev B) (fun _ => 0)) :
    SatisfiesInequalitySix (ev A) (ev B) ↔ ∃ L : RatFunc ℝ, IsRiccatiWitness (ev A) (ev B) L := by sorry

end HolonomicPositivity.Robust
