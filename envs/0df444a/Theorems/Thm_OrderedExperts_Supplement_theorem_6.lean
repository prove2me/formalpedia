-- Prove2me | Theorems.Thm_OrderedExperts_Supplement_theorem_6
-- name    : OrderedExperts.Supplement.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-18T07:05:57.171835+00:00
-- url     : https://prove2.me/theorems/9512c3c2-e474-42b6-a1cc-4dc420c6d4cf
-- title:
--   Theorem 6 — separated one-point lower bound
-- statement:
--   There are an absolute constant $c>0$ and an absolute horizon threshold $T_0$ such that, for every $n\ge2$, $T\ge T_0$, and randomized one-point learner, a deterministic oblivious separated-monotone instance with constant recommendations satisfies
--
--   $$
--   \mathbb E\operatorname{Reg}_T(F)\ge c\min\{\sqrt{nT},T^{2/3}\}.
--   $$
--
--   The bound captures the limit imposed by hiding a favorable coordinate while preserving monotonicity of the revealed component.
--
--   **Formalization Note** A separated one-point observation contains both component values at the queried rank. The learner is a conditional finite law; the hard component sequences are deterministic functions fixed before play.
--
--   Differences from the source:
--   - encoding: every randomized one-point learner and a deterministic oblivious instance → a conditional finite action law and fixed component functions; reason: this is the exact finite-history representation of the same interaction
--   - encoding: $\Omega(\min\{\sqrt{nT},T^{2/3}\})$ for all sufficiently large $T$ → a positive universal constant and a universal natural threshold before $n$, $T$, and the learner; reason: this is the literal uniform meaning supplied by Appendix D.4
--   - encoding: $T^{2/3}$ → real exponentiation `Real.rpow T (2/3)`; reason: $T>0$ in the theorem and the values coincide
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version), Theorem 6, p. 13; Appendix D.4, pp. 29–30

import Definitions.Def_OrderedExperts_Supplement_oneExpLoss
import Definitions.Def_OrderedExperts_Supplement_bestExpertLoss
import Definitions.Def_OrderedExperts_IsSepMonoLoss

namespace OrderedExperts.Supplement

/-- **Theorem 6 (Separated one-point lower bound).** Zuo, *Online Learning with Ordered Experts
(via Two-point Feedback)*, STOC 2027 submission (held version), Theorem 6, p. 13 and proof in
Appendix D.4, pp. 29--30.

There are an absolute positive constant and an absolute horizon threshold such that every
randomized one-point learner, for every sufficiently large `T`, suffers expected regret at least
`c min(√(nT), T^(2/3))` on a deterministic oblivious separated-monotone instance with constant
recommendations.

**Formalization Note.** A one-point separated observation contains the upward and downward
component values at the queried rank.  The exact finite conditional-law model includes every
randomized nonanticipating learner.  Both the constant and threshold precede the learner and the
hard deterministic sequence. -/
theorem theorem_6 :
    ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℕ, ∀ (n T : ℕ) [NeZero n],
      2 ≤ n → T₀ ≤ T →
      ∀ P : OnePointPolicy (Fin n) n (ℝ × ℝ),
        ∃ up down : ℕ → Fin n → ℝ,
          (∀ t < T, IsSepMonoLoss (up t) (down t)) ∧
          c * min (Real.sqrt ((n : ℝ) * T)) (Real.rpow T (2 / 3 : ℝ)) ≤
            let rs : ℕ → Fin n → Fin n := fun _ f ↦ f
            let loss : ℕ → Fin n → ℝ := fun t x ↦ up t x + down t x
            oneExpLoss P rs loss
                (fun t a ↦ (up t (chainPt rs t a), down t (chainPt rs t a))) T 0 [] -
              bestExpertLoss T rs loss := by sorry

end OrderedExperts.Supplement
