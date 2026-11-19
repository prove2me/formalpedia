-- Prove2me | Theorems.Thm_OrderedExperts_Supplement_theorem_7
-- name    : OrderedExperts.Supplement.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-18T07:11:42.941202+00:00
-- url     : https://prove2.me/theorems/1e72e28b-d37c-42a2-9320-7f855f621ffa
-- title:
--   Theorem 7 — one-point BV feedback
-- statement:
--   There are universal constants $c,C>0$ such that, whenever $2\le n\le T$, one one-point BV policy has regret at most $C\sqrt{nT}$ on every oblivious BV instance, while every one-point BV policy has some oblivious BV instance with regret at least $c\sqrt{nT}$. Thus
--
--   $$
--   R_T^{(1)}=\Theta(\sqrt{nT}).
--   $$
--
--   The lower-bound losses also admit a separated-monotone decomposition.
--
--   This identifies the one-point BV rate and records that the lower bound already occurs inside the more structured separated-monotone class.
--
--   **Formalization Note** The upper policy is chosen before recommendations and losses. The lower instance may depend on the learner but is fixed before play and reveals only aggregate losses.
--
--   Differences from the source:
--   - encoding: the minimax identity $R_T^{(1)}=\Theta(\sqrt{nT})$ → an upper policy valid for every instance and, for every policy, an existential hard instance, with universal constants; reason: these are exactly the two minimax inequalities without unsafe real infima or suprema
--   - encoding: randomized one-point policies and expected regret → conditional finite action laws and exact finite recursions; reason: the active chain is finite on every round
--   - encoding: the lower-bound action space used by the construction → `Fin n`, with arbitrary oblivious recommendations and losses that satisfy both predicates; reason: only the finite ordered active losses enter the testing argument
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version), Theorem 7, p. 14; Appendix D.5, p. 30

import Definitions.Def_OrderedExperts_Supplement_oneExpLoss
import Definitions.Def_OrderedExperts_Supplement_bestExpertLoss
import Definitions.Def_OrderedExperts_Supplement_IsBVLoss
import Definitions.Def_OrderedExperts_IsSepMonoLoss

namespace OrderedExperts.Supplement

/-- **Theorem 7 (One-point BV feedback).** Zuo, *Online Learning with Ordered Experts (via
Two-point Feedback)*, STOC 2027 submission (held version), Theorem 7, p. 14 and proof in
Appendix D.5, p. 30.

For `2 ≤ n ≤ T`, universal positive constants give both minimax directions: some one-point BV
policy has regret at most `C√(nT)` on every oblivious BV instance, while every such policy has an
oblivious BV instance with regret at least `c√(nT)`.  The lower-bound loss sequence also admits a
separated-monotone decomposition.

**Formalization Note.** The upper policy is chosen before recommendations and losses.  In the
lower clause, the instance may depend on the learner but is fixed before play, and the BV learner
sees only the aggregate loss.  This upper/lower quantifier pair is the minimax `Θ` assertion without
using a real infimum or supremum with default values. -/
theorem theorem_7 :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (n T : ℕ) [NeZero n], 2 ≤ n → n ≤ T →
        (∀ (A : Type*) [LinearOrder A] [BoundedOrder A],
          ∃ P : OnePointPolicy A n ℝ,
            ∀ (rec : ℕ → Fin n → A) (loss : ℕ → A → ℝ),
              (∀ t < T, IsBVLoss (rec t) (loss t)) →
              oneExpLoss P rec loss (fun t a ↦ loss t (chainPt rec t a)) T 0 [] -
                  bestExpertLoss T rec loss ≤
                C * Real.sqrt ((n : ℝ) * T)) ∧
        (∀ P : OnePointPolicy (Fin n) n ℝ,
          ∃ (rec : ℕ → Fin n → Fin n) (up down : ℕ → Fin n → ℝ),
            (∀ t < T, IsSepMonoLoss (up t) (down t)) ∧
            (∀ t < T, IsBVLoss (rec t) (fun x ↦ up t x + down t x)) ∧
            c * Real.sqrt ((n : ℝ) * T) ≤
              let loss : ℕ → Fin n → ℝ := fun t x ↦ up t x + down t x
              oneExpLoss P rec loss (fun t a ↦ loss t (chainPt rec t a)) T 0 [] -
                bestExpertLoss T rec loss) := by sorry

end OrderedExperts.Supplement
