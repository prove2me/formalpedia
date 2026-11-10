-- Prove2me | Theorems.Thm_NashOrTriangle_lemma_C3
-- name    : NashOrTriangle.lemma_C3
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:49:53.945195+00:00
-- url     : https://prove2.me/theorems/fa516f7e-0ac0-4ec2-8ec5-342e7f2cfe9a
-- title:
--   Lemma C.3 — a run with more than $F$ BR calls, or a failed check, reveals a $(t,\gamma)$-triangle (and its binary form)
-- statement:
--   Let $P$ be an algorithm in the oracle model, fix its input, and let $V$ be a property of finite (label-level) transcripts. Let $t \ge 2$, $\gamma \in \mathbb R$, $\delta \ge 0$ and $F \in \mathbb N$.
--
--   1. Suppose that on every finite game without a $(t, \gamma)$-triangle, and for all valid $\delta$-BR oracle answers, $P$ stops within $F$ BR calls with a transcript satisfying $V$. Run $P$ on any game, finite or not, with any $\delta$-BR oracle. If the run makes more than $F$ BR calls, or stops with a transcript violating $V$, then the strategies it has encountered contain a $(t, \gamma)$-triangle.
--   2. (Binary form.) Suppose that on every finite **binary** game without a $t$-triangle, and for all valid $\delta$-BR oracle answers, $P$ stops within $F$ BR calls with a transcript satisfying $V$. Run $P$ on any binary game. If the run makes more than $F$ BR calls, or stops with a transcript violating $V$, then the strategies it has encountered contain a $t$-triangle.
--
--   The lemma turns a budget for triangle-free finite games into an answer on arbitrary countable games: once the budget is exceeded or the final check fails, a triangle can be found among the finitely many strategies seen so far.
--
--   **Formalization Note** "Encountered strategies" at time $n$ are the known rows and columns of the state after $n$ steps. Transcripts record labels and payoff values only.
--
--   Differences from the source:
--   - reading: t unrestricted in the lemma → t ≥ 2; reason: the standing assumption k, t ≥ 2 of Definition 1.1 and Theorem 2.1; at t = 1 the literal lemma fails: every nonempty finite game has a (1, γ)-triangle, so the hypothesis is vacuous, while an algorithm making only maximizing ⊥ queries forever exceeds F calls without encountering any column
--   - generalization: the lemma for finite games without a (t, γ)-triangle → a second conjunct: finite binary games without a t-triangle in the hypothesis, a binary game and a t-triangle in the conclusion; reason: the proof of Theorem 2.1(a) applies the lemma in this binary form ("Lemma C.3 says that the O(F) strategies encountered contain a t-triangle"); the same restriction argument proves it
--   - encoding: valid oracle answers; a property of finite transcripts; the strategies encountered → BRAdversary N δ with the same δ ≥ 0 in hypothesis and conclusion; V : List Event → Prop on the label-level transcript; the rows and cols lists of the state; reason: the oracle model of §1.1; the transcript is what the algorithm sees
--   - encoding: A stops within F BR calls with a transcript satisfying V → HaltsWith P N adv x (fun s => s.brCalls ≤ F ∧ V s.transcript); reason: halting is the execution of a halt instruction; halted states do not change
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962…66f7), Appendix C, Lemma C.3, p.25 (PDF p.26); binary use in the proof of Theorem 2.1(a), p.25 (PDF p.26)

import Mathlib
import Definitions.Def_NashOrTriangle_OracleMachine
import Definitions.Def_NashOrTriangle_HaltsWith
import Definitions.Def_NashOrTriangle_IsPayoff
import Definitions.Def_NashOrTriangle_IsBinary
import Definitions.Def_NashOrTriangle_HasTriangle
import Definitions.Def_NashOrTriangle_HasMarginTriangle

namespace NashOrTriangle

/-- **Lemma C.3** (a long run gives a triangle). Let `P` be an algorithm in the oracle model and
`V` a property of finite transcripts. Suppose that on every finite game without a
`(t, γ)`-triangle, and for all valid oracle answers, `P` stops within `F` BR calls with a
transcript satisfying `V`. Run `P` on any game, finite or not: if the run makes more than `F`
BR calls, or stops with a transcript violating `V`, then the strategies it has encountered
contain a `(t, γ)`-triangle. The second clause is the binary form used in the proof of
Theorem 2.1(a): finite binary games without a `t`-triangle in the hypothesis, a binary game and
a `t`-triangle in the conclusion.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), Appendix C, Lemma C.3, printed p. 25 (PDF p. 26); binary use in the proof of
Theorem 2.1(a), printed p. 25 (PDF p. 26).

**Formalization Note** "Valid oracle answers" are `δ`-BR oracles (`BRAdversary M δ`) for the same
`δ ≥ 0` in hypothesis and conclusion. Transcripts are label-level (`List Event`), i.e. what the
algorithm sees. The encountered strategies at time `n` are the known rows and columns of the
state at time `n`. `t ≥ 2` is the standing assumption of Definition 1.1 and Theorem 2.1. -/
theorem lemma_C3 (P : Program) (x : ℤ → ℝ) (t : ℕ) (ht : 2 ≤ t) (γ δ : ℝ) (hδ : 0 ≤ δ)
    (F : ℕ) (V : List Event → Prop) :
    ((∀ {H₁ H₂ : Type} [Fintype H₁] [Fintype H₂] [Nonempty H₁] [Nonempty H₂]
        (N : H₁ → H₂ → ℚ), IsPayoff N → ¬ HasMarginTriangle N t γ → ∀ adv : BRAdversary N δ,
        HaltsWith P N adv x (fun s => s.brCalls ≤ F ∧ V s.transcript)) →
      ∀ {A B : Type} [Countable A] [Countable B] [Nonempty A] [Nonempty B] (M : A → B → ℚ),
        IsPayoff M → ∀ adv : BRAdversary M δ, ∀ n : ℕ,
        (F < (run P M adv x n).brCalls ∨
          ((run P M adv x n).output.isSome ∧ ¬ V (run P M adv x n).transcript)) →
        ∃ a : Fin t → A, ∃ b : Fin t → B, (∀ i, a i ∈ (run P M adv x n).rows) ∧
          (∀ j, b j ∈ (run P M adv x n).cols) ∧ IsMarginTriangle M γ a b) ∧
    ((∀ {H₁ H₂ : Type} [Fintype H₁] [Fintype H₂] [Nonempty H₁] [Nonempty H₂]
        (N : H₁ → H₂ → ℚ), IsPayoff N → IsBinary N → ¬ HasTriangle N t →
        ∀ adv : BRAdversary N δ,
        HaltsWith P N adv x (fun s => s.brCalls ≤ F ∧ V s.transcript)) →
      ∀ {A B : Type} [Countable A] [Countable B] [Nonempty A] [Nonempty B] (M : A → B → ℚ),
        IsPayoff M → IsBinary M → ∀ adv : BRAdversary M δ, ∀ n : ℕ,
        (F < (run P M adv x n).brCalls ∨
          ((run P M adv x n).output.isSome ∧ ¬ V (run P M adv x n).transcript)) →
        ∃ a : Fin t → A, ∃ b : Fin t → B, (∀ i, a i ∈ (run P M adv x n).rows) ∧
          (∀ j, b j ∈ (run P M adv x n).cols) ∧ IsTriangle M a b) := by sorry

end NashOrTriangle
