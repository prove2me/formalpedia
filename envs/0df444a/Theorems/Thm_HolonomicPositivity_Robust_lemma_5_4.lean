-- Prove2me | Theorems.Thm_HolonomicPositivity_Robust_lemma_5_4
-- name    : HolonomicPositivity.Robust.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:31:48.493709+00:00
-- url     : https://prove2.me/theorems/06cea72e-2298-4895-b7c7-ab72b86ff461
-- title:
--   Lemma 5.4 — existence of the rational scaling function $S$
-- statement:
--   Let $P,Q\in\mathbb R(x)$ have no poles on $\mathbb N$, satisfy $Q(n)\ne0$ for all $n\in\mathbb N$, and satisfy condition (II) of Theorem 3.1. Then there is $S\in\mathbb R(x)$ such that, with
--
--   $$B(x):=1-S(x+2),\qquad A(x):=B(x)S(x+1)+P(x),\qquad C(x):=A(x)S(x)+Q(x),$$
--
--   all of the following hold in the eventual order as $x\to+\infty$:
--
--   1. $S(x)\ge0$;
--   2. $B>0$, and $A,B$ satisfy both equivalent conditions of Lemma 5.3, namely $\frac{A(x)}{B(x)B(x-1)}\ge-\frac14-\frac1{16x^2}+O(x^{-3})$, and there is $L\in\mathbb R(x)$ with $0<L(x+1)<B(x)$ and $L(x)(B(x)-L(x+1))+A(x)\ge0$;
--   3. $C(x)\ge0$.
--
--   This reduces the third-order threshold to a second-order inequality for the scaled difference $\Delta_Sf$.
--
--   Differences from the source:
--   - reading: "$A,B$ satisfy one (i.e., both) of the equivalent conditions in Lemma 5.3", whose standing assumption is $B>0$ → the conjunction of $B>0$ and both conditions; reason: this is the source's "both", and it does not rely on importing Lemma 5.3.
--   - encoding: the no-pole assumption on $P,Q$ is a global convention (PDF p.1) → explicit hypotheses on the reduced denominators; reason: the lemma's $P,Q$ are the coefficients of the recurrence, to which the source's convention applies.
--   - encoding: $B,A,C\in\mathbb R(x)$ → the real functions $x\mapsto1-S(x+2)$, and so on, built by evaluating $S,P,Q$; reason: these agree with the rational functions except at finitely many poles, and every relation they enter is eventual.
--   - encoding: "let (7) be the Taylor expansion" → existentially quantified coefficients satisfying (7) inside condition (II); reason: under the two comparisons on $P$ the expansion exists and is unique, so no instance changes.
-- source:
--   Fugen Hagihara, STOC 2027 submission #328 (October 2026), Lemma 5.4, PDF p.10 (printed XX:10).

import Mathlib
import Definitions.Def_HolonomicPositivity_Robust_Conditions

namespace HolonomicPositivity.Robust

/-- Lemma 5.4, PDF p.10 (XX:10). Clause (2) contains the standing assumption `B > 0` of Lemma 5.3
and both of its equivalent conditions ("one (i.e., both)"). -/
theorem lemma_5_4 (P Q : RatFunc ℝ) (hP : NoPolesOnNat P) (hQ : NoPolesOnNat Q)
    (hQ0 : ∀ n : ℕ, ev Q n ≠ 0) (hII : ConditionII P Q) :
    ∃ S : RatFunc ℝ,
      EventuallyGE (ev S) (fun _ => 0) ∧
      (EventuallyGT (scaledB S) (fun _ => 0) ∧
        SatisfiesInequalitySix (scaledA P S) (scaledB S) ∧
        ∃ L : RatFunc ℝ, IsRiccatiWitness (scaledA P S) (scaledB S) L) ∧
      EventuallyGE (scaledC P Q S) (fun _ => 0) := by sorry

end HolonomicPositivity.Robust
