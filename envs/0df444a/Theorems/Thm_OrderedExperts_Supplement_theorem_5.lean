-- Prove2me | Theorems.Thm_OrderedExperts_Supplement_theorem_5
-- name    : OrderedExperts.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-18T07:01:26.839196+00:00
-- url     : https://prove2.me/theorems/f77d0c8b-db45-48e1-9730-8134569ea0a0
-- title:
--   Theorem 5 — needle lower bound
-- statement:
--   There is an absolute constant $c>0$ such that for every $n,T\ge2$ and every randomized two-point algorithm for the BV problem, some oblivious BV instance satisfies
--
--   $$
--   \mathbb E\operatorname{Reg}_T(F)\ge c\min\{n,T\}.
--   $$
--
--   This is the search cost of finding the hidden zero-loss action when each round can inspect at most two candidates.
--
--   **Formalization Note** The learner observes only the two aggregate losses. Recommendations and losses are fixed before interaction and may depend on the learner.
--
--   Differences from the source:
--   - encoding: arbitrary randomized two-point algorithms and expected regret → conditional finite pair laws and an exact finite recursion; reason: this is the same nonanticipating learner class on finite active chains
--   - encoding: $\Omega(\min\{n,T\})$ → one positive constant quantified before $n$, $T$, the learner, and the hard instance; reason: Appendix C.3 supplies a uniform constant (indeed $1/24$)
--   - encoding: an unspecified ordered action space for the hard instance → the finite ordered action space `Fin n`; reason: the needle construction uses only finitely many ordered candidates
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version), Theorem 5, p. 13; Appendix C.3, p. 26

import Definitions.Def_OrderedExperts_Supplement_twoExpLoss
import Definitions.Def_OrderedExperts_Supplement_bestExpertLoss
import Definitions.Def_OrderedExperts_Supplement_IsBVLoss

namespace OrderedExperts.Supplement

/-- **Theorem 5 (Needle lower bound).** Zuo, *Online Learning with Ordered Experts (via
Two-point Feedback)*, STOC 2027 submission (held version), Theorem 5, p. 13 and proof in
Appendix C.3, p. 26.

One absolute positive constant works for every two-point BV learner: a fixed oblivious BV loss
sequence forces expected regret at least `c min(n,T)`.

**Formalization Note.** The finite action set is `Fin n`.  The learner observes only the two
aggregate losses.  The existential recommendations and loss sequence may depend on the learner
but are fixed before interaction. -/
theorem theorem_5 :
    ∃ c : ℝ, 0 < c ∧ ∀ (n T : ℕ) [NeZero n], 2 ≤ n → 2 ≤ T →
      ∀ P : TwoPointPolicy (Fin n) n (ℝ × ℝ),
        ∃ (rec : ℕ → Fin n → Fin n) (loss : ℕ → Fin n → ℝ),
          (∀ t < T, IsBVLoss (rec t) (loss t)) ∧
          c * (min n T : ℕ) ≤
            twoExpLoss P rec loss
                (fun t a b ↦ (loss t (chainPt rec t a), loss t (chainPt rec t b))) T 0 [] -
              bestExpertLoss T rec loss := by sorry

end OrderedExperts.Supplement
