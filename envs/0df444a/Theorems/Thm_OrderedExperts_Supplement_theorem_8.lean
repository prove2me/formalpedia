-- Prove2me | Theorems.Thm_OrderedExperts_Supplement_theorem_8
-- name    : OrderedExperts.Supplement.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-18T07:17:06.852875+00:00
-- url     : https://prove2.me/theorems/83afaaf0-eb32-4805-ad26-e68dd0fa4a6a
-- title:
--   Theorem 8 — full-information benchmark
-- statement:
--   There are universal constants $c,C>0$ such that, whenever $\log_2 n\le T$, one full-information policy has regret at most $C\sqrt{T\log n}$ on every oblivious instance in either loss class, while every full-information policy has a constant-recommendation instance belonging to both classes with regret at least $c\sqrt{T\log n}$. Hence
--
--   $$
--   R_T^{\mathrm{full}}=\Theta(\sqrt{T\log n})
--   $$
--
--   in both the separated-monotone and BV problems.
--
--   The lower bound survives even though the learner sees the entire current active loss vector after acting.
--
--   **Formalization Note** The same upper policy covers both classes and chooses before current full information is appended to its history. The lower sequence is deterministic and oblivious, with each expert permanently attached to its action.
--
--   Differences from the source:
--   - encoding: the two minimax $\Theta$ identities → one universal upper policy for both classes and a universal lower clause whose hard instance lies in both classes; reason: this states both minimax directions without default-valued infima or suprema
--   - encoding: randomized full-information policies and expected regret → conditional finite action laws and exact finite recursions with the current vector revealed only after acting; reason: this preserves the source's timing and learner class
--   - encoding: base-two logarithm in the horizon condition and an unspecified logarithm in the rate → $\log n/\log 2\le T$ and natural $\log n$ in the rate; reason: the condition is exactly base two and changing the rate's log base only changes universal constants
--   - encoding: the proof's balanced-tree hard action set → `Fin n` with fixed identity recommendations; reason: unused actions can duplicate a leaf loss, so the ordered active instance is unchanged up to relabeling
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version), Theorem 8, p. 14; Appendix D.1, pp. 27–28

import Definitions.Def_OrderedExperts_Supplement_fullExpLoss
import Definitions.Def_OrderedExperts_Supplement_bestExpertLoss
import Definitions.Def_OrderedExperts_Supplement_IsBVLoss
import Definitions.Def_OrderedExperts_IsSepMonoLoss

namespace OrderedExperts.Supplement

/-- **Theorem 8 (Full-information benchmark).** Zuo, *Online Learning with Ordered Experts (via
Two-point Feedback)*, STOC 2027 submission (held version), Theorem 8, p. 14 and proof in
Appendix D.1, pp. 27--28.

Whenever `log₂ n ≤ T`, the full-information minimax regret in both the separated-monotone and
BV problems is between universal positive multiples of `√(T log n)`.  The lower-bound instance
belongs to both loss classes and keeps every expert on one fixed action on every round.

**Formalization Note.** One full-information policy is required to upper-bound both classes; it is
chosen before recommendations and losses.  The lower instance is chosen after the learner but is
an oblivious deterministic sequence.  The policy chooses before the current full loss vector is
added to its history.  Natural logarithms replace base-two logarithms only inside the rate, which
changes universal constants; the horizon hypothesis retains `log n / log 2`. -/
theorem theorem_8 :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (n T : ℕ) [NeZero n], 2 ≤ n → Real.log n / Real.log 2 ≤ T →
        (∀ (A : Type*) [LinearOrder A] [BoundedOrder A],
          ∃ P : FullInfoPolicy A n,
            (∀ (rec : ℕ → Fin n → A) (up down : ℕ → A → ℝ),
              (∀ t < T, IsSepMonoLoss (up t) (down t)) →
              let loss : ℕ → A → ℝ := fun t x ↦ up t x + down t x
              fullExpLoss P rec loss T 0 [] - bestExpertLoss T rec loss ≤
                C * Real.sqrt ((T : ℝ) * Real.log n)) ∧
            (∀ (rec : ℕ → Fin n → A) (loss : ℕ → A → ℝ),
              (∀ t < T, IsBVLoss (rec t) (loss t)) →
              fullExpLoss P rec loss T 0 [] - bestExpertLoss T rec loss ≤
                C * Real.sqrt ((T : ℝ) * Real.log n))) ∧
        (∀ P : FullInfoPolicy (Fin n) n,
          ∃ up down : ℕ → Fin n → ℝ,
            (∀ t < T, IsSepMonoLoss (up t) (down t)) ∧
            (∀ t < T, IsBVLoss (fun f : Fin n ↦ f) (fun x ↦ up t x + down t x)) ∧
            c * Real.sqrt ((T : ℝ) * Real.log n) ≤
              let rs : ℕ → Fin n → Fin n := fun _ f ↦ f
              let loss : ℕ → Fin n → ℝ := fun t x ↦ up t x + down t x
              fullExpLoss P rs loss T 0 [] - bestExpertLoss T rs loss) := by sorry

end OrderedExperts.Supplement
