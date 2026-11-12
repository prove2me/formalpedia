-- Prove2me | Theorems.Thm_HolonomicPositivity_Robust_lemma_5_1
-- name    : HolonomicPositivity.Robust.lemma_5_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:31:33.584206+00:00
-- url     : https://prove2.me/theorems/562b33e2-fec5-45a3-9e32-a8488bfbc86e
-- title:
--   Lemma 5.1 — invariance of the positivity certificate
-- statement:
--   Let $P,Q\in\mathbb R(x)$ have no poles on $\mathbb N$, satisfy $Q(n)\ne0$ for all $n\in\mathbb N$, and satisfy condition (II) of Theorem 3.1. Then there are $S,L\in\mathbb R(x)$ and $N\in\mathbb N$ such that $S,L$ have no poles at integers $n\ge N$ and, for every real sequence $f$ solving
--
--   $$f(n+3)=f(n+2)+P(n)f(n+1)+Q(n)f(n),$$
--
--   and every $n\ge N$,
--
--   $$\operatorname{Certificate}(n)\implies\operatorname{Certificate}(n+1),$$
--
--   where $\operatorname{Certificate}(n)$ is $f(n)>0\wedge\Delta_Sf(n)>0\wedge\Delta_L\Delta_Sf(n)>0$.
--
--   The witnesses $S,L,N$ are chosen before $f$, uniformly in the solution. The lemma supplies the invariant region used for case (II) of the goal theorem.
--
--   Differences from the source:
--   - encoding: the no-pole assumption on $P,Q$ is a global convention (PDF p.1) → explicit hypotheses on the reduced denominators; reason: Lean evaluates at a pole to a default value, and the source's convention covers all coefficients of the recurrence.
--   - encoding: Lemma 5.1's sentence is silent on poles of $S,L$, and the note in §4 (PDF p.9, lines 296-297) requires $N$ beyond them → a conclusion clause that $S,L$ have no poles at natural $n\ge N$; reason: this is the source's own specification of $N$, written where Lean needs it.
--   - encoding: "let (7) be the Taylor expansion" → existentially quantified coefficients satisfying (7) inside condition (II); reason: under the two comparisons on $P$ the expansion exists and is unique, so no instance changes.
-- source:
--   Fugen Hagihara, STOC 2027 submission #328 (October 2026), Lemma 5.1, PDF p.9 (printed XX:9); certificate (8) and the note on poles, PDF p.9.

import Mathlib
import Definitions.Def_HolonomicPositivity_Robust_Recurrence
import Definitions.Def_HolonomicPositivity_Robust_Conditions

namespace HolonomicPositivity.Robust

/-- Lemma 5.1, PDF p.9 (XX:9). The witnesses `S, L, N` are chosen before the solution `f`; `N` lies
beyond the poles of `S` and `L`, as the §4 note requires (PDF p.9, lines 296–297). -/
theorem lemma_5_1 (P Q : RatFunc ℝ) (hP : NoPolesOnNat P) (hQ : NoPolesOnNat Q)
    (hQ0 : ∀ n : ℕ, ev Q n ≠ 0) (hII : ConditionII P Q) :
    ∃ (S L : RatFunc ℝ) (N : ℕ),
      (∀ n : ℕ, N ≤ n → S.denom.eval (n : ℝ) ≠ 0 ∧ L.denom.eval (n : ℝ) ≠ 0) ∧
      ∀ f : ℕ → ℝ, IsSolution P Q f →
        ∀ n : ℕ, N ≤ n → Certificate S L f n → Certificate S L f (n + 1) := by sorry

end HolonomicPositivity.Robust
