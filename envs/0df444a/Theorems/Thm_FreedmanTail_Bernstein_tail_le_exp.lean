-- Prove2me | Theorems.Thm_FreedmanTail_Bernstein_tail_le_exp
-- name    : FreedmanTail.Bernstein.tail_le_exp
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T09:54:53.4699+00:00
-- url     : https://prove2.me/theorems/030199b4-890c-4d87-832d-fc4945089ef7
-- title:
--   Proof of (4.1) — P{S_n ≥ a and T_n ≤ b for some n} ≤ exp[−λa + e(λ)b] for every λ ≥ 0
-- statement:
--   In the setting of Proposition (3.3), with condition (3.4) (increments $X_n\le1$ a.e., square integrable and $\mathcal F_n$-measurable, with $E\{X_n\mid\mathcal F_{n-1}\}\le0$ a.e.), let $a>0$ and $b>0$, and let
--   $$A=\{S_n\ge a\ \text{and}\ T_n\le b\ \text{for some } n=1,2,\dots\}.$$
--   Then for every $\lambda\ge0$, with $e(\lambda)=e^\lambda-1-\lambda$,
--   $$P\{A\}\le\exp[-\lambda a+e(\lambda)b].$$
--
--   The event $A$ is a union over all times $n\ge1$, so the bound is uniform in time. Optimizing over $\lambda$ gives Theorem (4.1).
--
--   **Formalization Note** $P\{A\}$ is the measure of the set $A$ (Mathlib's outer measure; $A$ is measurable under the hypotheses). Square integrability of the $X_n$ is assumed for the reason given in Definition (1.2).
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975), pp. 107–108 (PDF pp. 8–9), proof of (4.1) Theorem, last display of p. 107 and the first words of p. 108

import Mathlib
import Definitions.Def_FreedmanTail_Bernstein_Exponents
import Definitions.Def_FreedmanTail_Bernstein_PartialSums

open MeasureTheory ProbabilityTheory

namespace FreedmanTail.Bernstein

/-- Freedman (1975), proof of (4.1) Theorem, pp. 107–108: under (3.4), for positive `a, b`
and every `λ ≥ 0`, `P{S_n ≥ a and T_n ≤ b for some n} ≤ exp[−λa + e(λ)b]`. -/
theorem tail_le_exp {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ)
    (hmeas : ∀ n, 1 ≤ n → StronglyMeasurable[ℱ n] (X n))
    (hL2 : ∀ n, 1 ≤ n → MemLp (X n) 2 P)
    (hle : ∀ n, 1 ≤ n → X n ≤ᵐ[P] 1)
    (hdrift : ∀ n, 1 ≤ n → P[X n | ℱ (n - 1)] ≤ᵐ[P] 0)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (lam : ℝ) (hlam : 0 ≤ lam) :
    P {ω | ∃ n, 1 ≤ n ∧ a ≤ S X n ω ∧ T ℱ X P n ω ≤ b}
      ≤ ENNReal.ofReal (Real.exp (-lam * a + e lam * b)) := by sorry

end FreedmanTail.Bernstein
