-- Prove2me | Theorems.Thm_OnlineConvexOpt_Introduction_no_deterministic_algorithm_beats_double_mistakes
-- name    : OnlineConvexOpt.Introduction.no_deterministic_algorithm_beats_double_mistakes
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T05:06:11.441929+00:00
-- url     : https://prove2.me/theorems/328c2530-01f2-4ac4-a4b5-178ab3cd4655
-- title:
--   Theorem 1.1 — No deterministic algorithm beats 2L mistakes
-- statement:
--   **Theorem 1.1** (Hazan, p. 8). Let $L \le T/2$ denote the number of mistakes made by
--   the best expert in hindsight. Then there does not exist a deterministic algorithm that can
--   guarantee less than $2L$ mistakes.
--
--   This is formalized via the book's own two-expert adversary construction (the proof Hazan
--   gives): one expert always predicts the book's action $A$ (`true`), the other always predicts
--   $B$ (`false`). A deterministic algorithm is modelled as a causal map
--   `alg : (ℕ → Bool) → ℕ → Bool` from an outcome sequence to its own prediction sequence, where the
--   prediction at round $t$ depends only on the outcomes strictly before $t$ (causality is what
--   makes the adversary construction — choosing each outcome *after* seeing the algorithm's
--   prediction — well-defined). For every causal `alg` and every horizon `T`, the theorem exhibits
--   an outcome sequence on which `alg` errs on *every* round (`algMistakes = T`) while the best
--   expert's mistake count `L` is at most `T/2` — since the two experts' mistake counts always sum
--   to `T`, this single witness shows `T ≥ 2L`, matching the book's "cannot guarantee fewer than
--   $2L$ mistakes":
--
--   $$
--   \forall\, \text{alg causal}, \forall T,\ \exists\, \text{outcome}:\quad
--   M_T(\text{alg}) = T \ \wedge\ T \ge 2 \min\bigl(M_T(A),\, M_T(B)\bigr).
--   $$
--
--   **Formalization Note.** A direct transcription of the book's sentence as
--   `¬∃ alg, ∀ outcome, mistakes(outcome) < 2L(outcome)` is a trivializing formalization: any
--   *constant* outcome sequence gives `L = 0`, so that negation is provable in one line from
--   `mistakes ≥ 0`, without using causality or the adversary construction at all. The
--   `algMistakes = T` conjunct blocks this shortcut — it is false on an outcome sequence the
--   algorithm predicts correctly, so proving it for a specific `alg` forces the actual
--   causality-driven adversary construction the book gives. This instantiates the book's proof at
--   its own two-expert construction rather than a fully general $N$-expert adversary claim — the
--   exact scope the book's argument establishes.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 8, Theorem 1.1

import Mathlib import Definitions.Def_OnlineConvexOpt_Introduction_MistakeCounts

namespace OnlineConvexOpt.Introduction

/-- **Theorem 1.1**, Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 8.

"Let `L ≤ T/2` denote the number of mistakes made by the best expert in hindsight. Then there
does not exist a deterministic algorithm that can guarantee less than `2L` mistakes."

The theorem is stated as the book's proof actually establishes it: for every causal `alg`
and every horizon `T`, the adversary (which plays, at each round, whichever outcome `alg` did
*not* predict — well-defined by causality, since `alg`'s round-`t` prediction depends only on
already-fixed earlier outcomes) forces `alg` to err on literally every round, `algMistakes = T`;
since the two experts' mistake counts always sum to `T`, their minimum `L` is always `≤ T/2`, so
this single witness shows `T ≥ 2 L`, i.e. `alg`'s own mistake count is at least twice the best
expert's, matching the book's "cannot guarantee fewer than `2L` mistakes" (a bound that must
hold against every possible outcome sequence, refuted by exhibiting one on which it fails).

A direct transcription of "`¬∃ alg, ∀ outcome, mistakes(outcome) < 2 L(outcome)`" is a
trivializing formalization: any *constant* outcome sequence gives `L = 0`, so any such
transcription is provable in one line from `mistakes ≥ 0`, without using causality or the
adversary construction at all (Nat-valued mistake counts can never satisfy `< 0`). The
`algMistakes _ _ T = T` conjunct below blocks that shortcut: it is false for an arbitrary
outcome (an algorithm that happens to predict a constant outcome correctly makes zero mistakes
on it), so establishing it for a *specific* algorithm requires actually building the
causality-driven adversarial sequence. -/
theorem no_deterministic_algorithm_beats_double_mistakes
    (alg : (ℕ → Bool) → ℕ → Bool)
    (halg : ∀ outcome₁ outcome₂ : ℕ → Bool, ∀ t : ℕ,
      (∀ s, s < t → outcome₁ s = outcome₂ s) → alg outcome₁ t = alg outcome₂ t)
    (T : ℕ) :
    ∃ outcome : ℕ → Bool,
      algMistakes (alg outcome) outcome T = T ∧
      (T : ℝ) ≥
        2 * (min ((Finset.range T).filter (fun t => outcome t = false)).card
                  ((Finset.range T).filter (fun t => outcome t = true)).card : ℝ) := by sorry

end OnlineConvexOpt.Introduction
