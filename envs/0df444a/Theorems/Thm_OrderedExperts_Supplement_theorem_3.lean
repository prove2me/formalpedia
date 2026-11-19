-- Prove2me | Theorems.Thm_OrderedExperts_Supplement_theorem_3
-- name    : OrderedExperts.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-18T06:51:23.701437+00:00
-- url     : https://prove2.me/theorems/90ca50f1-ebe4-4189-acfa-8b96e0bec650
-- title:
--   Theorem 3 — two-point lower bound
-- statement:
--   There is an absolute constant $c>0$ such that for every number of experts $n\ge2$, every horizon $T\ge2$, and every randomized two-point learner, some deterministic oblivious separated-monotone instance with constant recommendations satisfies
--
--   $$
--   \mathbb E\operatorname{Reg}_T(F)\ge c\sqrt T\,\log\min\{n,\sqrt T\}.
--   $$
--
--   Every hard loss also has total variation at most one. The same lower bound holds for a BV learner that observes only the two aggregate losses.
--
--   The theorem shows that two simultaneous queries do not remove the logarithmic price of locating the hidden dyadic path.
--
--   **Formalization Note** Separated feedback returns both monotone components at both queried ranks, while BV feedback returns only their sums. Each learner is a conditional finite law, and its hard sequence is fixed before play.
--
--   Differences from the source:
--   - encoding: randomized nonanticipating learners and expected regret → conditional finite probability laws and exact finite recursions; reason: every round has finitely many active ranks, so this is the same learner class and expectation
--   - encoding: the proof's hard action space $[0,1]$ with fixed expert points → `Fin n` with one fixed action per expert; reason: only the ordered active points and their losses enter the interaction, so order-preserving relabeling gives the same instances
--   - encoding: $\Omega(\sqrt T\log\min\{n,\sqrt T\})$ and its BV consequence → one positive constant before all parameters and separate separated/BV learner clauses; reason: this is the literal uniform-constant meaning of the two assertions
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version), Theorem 3, p. 11; Appendix B.3, pp. 21–24

import Definitions.Def_OrderedExperts_Supplement_twoExpLoss
import Definitions.Def_OrderedExperts_Supplement_bestExpertLoss
import Definitions.Def_OrderedExperts_Supplement_IsBVLoss
import Definitions.Def_OrderedExperts_IsSepMonoLoss

open Finset

namespace OrderedExperts.Supplement

/-- **Theorem 3 (Two-point lower bound).** Zuo, *Online Learning with Ordered Experts (via
Two-point Feedback)*, STOC 2027 submission (held version), Theorem 3, p. 11 and proof in
Appendix B.3, pp. 21--24.

There is one absolute positive constant such that, for every `n = |F| ≥ 2`, `T ≥ 2`, and
every randomized two-point learner, a deterministic oblivious separated-monotone instance with
constant recommendations forces expected regret at least
`c √T log(min(n,√T))`.  The hard losses also have total variation at most one.  The same
lower bound is asserted separately for a BV learner that observes only the two aggregate losses.

**Formalization Note.** Experts and the fixed actions are both `Fin n`; round `t` is zero-based.
The two clauses distinguish the richer separated observation (both components at both points) from
the BV observation (only the two sums).  Their existential instances may depend on the learner but
are fixed functions before interaction.  `c` is quantified before `n`, `T`, and the learner. -/
theorem theorem_3 :
    ∃ c : ℝ, 0 < c ∧
      (∀ (n T : ℕ) [NeZero n], 2 ≤ n → 2 ≤ T →
        ∀ P : TwoPointPolicy (Fin n) n ((ℝ × ℝ) × (ℝ × ℝ)),
          ∃ up down : ℕ → Fin n → ℝ,
            (∀ t < T, IsSepMonoLoss (up t) (down t)) ∧
            (∀ t < T, IsBVLoss (fun f : Fin n ↦ f) (fun x ↦ up t x + down t x)) ∧
            c * Real.sqrt T * Real.log (min (n : ℝ) (Real.sqrt T)) ≤
              let rs : ℕ → Fin n → Fin n := fun _ f ↦ f
              let loss : ℕ → Fin n → ℝ := fun t x ↦ up t x + down t x
              twoExpLoss P rs loss
                  (fun t a b ↦
                    ((up t (chainPt rs t a), down t (chainPt rs t a)),
                     (up t (chainPt rs t b), down t (chainPt rs t b)))) T 0 [] -
                bestExpertLoss T rs loss) ∧
      (∀ (n T : ℕ) [NeZero n], 2 ≤ n → 2 ≤ T →
        ∀ P : TwoPointPolicy (Fin n) n (ℝ × ℝ),
          ∃ up down : ℕ → Fin n → ℝ,
            (∀ t < T, IsSepMonoLoss (up t) (down t)) ∧
            (∀ t < T, IsBVLoss (fun f : Fin n ↦ f) (fun x ↦ up t x + down t x)) ∧
            c * Real.sqrt T * Real.log (min (n : ℝ) (Real.sqrt T)) ≤
              let rs : ℕ → Fin n → Fin n := fun _ f ↦ f
              let loss : ℕ → Fin n → ℝ := fun t x ↦ up t x + down t x
              twoExpLoss P rs loss
                  (fun t a b ↦ (loss t (chainPt rs t a), loss t (chainPt rs t b))) T 0 [] -
                bestExpertLoss T rs loss) := by sorry

end OrderedExperts.Supplement
