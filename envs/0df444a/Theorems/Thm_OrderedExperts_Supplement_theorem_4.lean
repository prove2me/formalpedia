-- Prove2me | Theorems.Thm_OrderedExperts_Supplement_theorem_4
-- name    : OrderedExperts.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-18T06:56:03.805699+00:00
-- url     : https://prove2.me/theorems/77b46124-dcef-427b-a268-1ba45b1fd303
-- title:
--   Theorem 4 — BV two-point upper bound
-- statement:
--   Let $n=|F|$, $\Lambda=1+\log(nT)$,
--
--   $$
--   \eta=\sqrt{\frac{\log n}{\Lambda^2T}},\qquad \mu=12\eta\Lambda.
--   $$
--
--   There are absolute constants $C_1,C_2>0$ such that Algorithm 3, on every oblivious BV loss sequence and arbitrary current recommendations, satisfies
--
--   $$
--   \mathbb E\operatorname{Reg}_T(F)
--   \le C_1\bigl(\Lambda\sqrt{T\log n}+n\Lambda\log T\bigr)
--   \le C_2(\sqrt T+n)\Lambda^2.
--   $$
--
--   Thus its regret is $\widetilde O(\sqrt T+n)$ while retaining the paper's full two-term bound.
--
--   **Formalization Note** Algorithm 3 is the exact endpoint-flow pair sampler and robust mirror-descent minimizer on the open simplex. Its expectation is the exact recursion over the aggregate BV feedback history.
--
--   Differences from the source:
--   - encoding: randomized Algorithm 3 and its expected regret → an exact conditional pair law, weight-state update, and finite expectation recursion; reason: this exposes precisely the information and randomness used by the printed algorithm
--   - encoding: $O(\Lambda\sqrt{T\log n}+n\Lambda\log T)=\widetilde O(\sqrt T+n)$ → two universal constants with the soft-O consequence bounded by $(\sqrt T+n)\Lambda^2$; reason: $\Lambda^2$ is a concrete polylogarithmic factor implied by the displayed two-term bound
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version), Theorem 4, p. 12; Appendix C.2, pp. 25–26

import Definitions.Def_OrderedExperts_Supplement_Algorithm3Run
import Definitions.Def_OrderedExperts_Supplement_twoExpLoss
import Definitions.Def_OrderedExperts_Supplement_bestExpertLoss
import Definitions.Def_OrderedExperts_Supplement_IsBVLoss

namespace OrderedExperts.Supplement

/-- **Theorem 4 (BV two-point upper bound).** Zuo, *Online Learning with Ordered Experts (via
Two-point Feedback)*, STOC 2027 submission (held version), Theorem 4, p. 12 and proof in
Appendix C.2, pp. 25--26.

Let `Λ = 1 + log(nT)`, `η = √(log n / (Λ²T))`, and `μ = 12ηΛ`.  Algorithm 3 has expected
regret bounded by one absolute constant times
`Λ√(T log n) + nΛ log T`; consequently it is bounded by a polylogarithmic factor times
`√T + n`.

**Formalization Note.** `Algorithm3Run` is the exact endpoint-flow sampler and robust
mirror-descent update.  The expectation is the finite recursion over its pair laws.  The second
inequality spells out the displayed soft-O consequence with the concrete polylogarithmic factor
`Λ²`; both constants are chosen before the action space and instance. -/
theorem theorem_4 :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ C₂ : ℝ, 0 < C₂ ∧
      ∀ (A : Type*) [LinearOrder A] [BoundedOrder A] (n T : ℕ) [NeZero n],
        2 ≤ n → 2 ≤ T →
        let Λ : ℝ := 1 + Real.log ((n : ℝ) * T)
        let η : ℝ := Real.sqrt (Real.log n / (Λ ^ 2 * T))
        let μ : ℝ := 12 * η * Λ
        ∃ R : Algorithm3Run A n T η μ,
          ∀ (rec : ℕ → Fin n → A) (loss : ℕ → A → ℝ),
            (∀ t < T, IsBVLoss (rec t) (loss t)) →
            let regret := twoExpLoss R.policy rec loss
                (fun t a b ↦ (loss t (chainPt rec t a), loss t (chainPt rec t b))) T 0 [] -
              bestExpertLoss T rec loss
            regret ≤ C₁ *
                (Λ * Real.sqrt ((T : ℝ) * Real.log n) + (n : ℝ) * Λ * Real.log T) ∧
              regret ≤ C₂ * (Real.sqrt T + n) * Λ ^ 2 := by sorry

end OrderedExperts.Supplement
