-- Prove2me | Theorems.Thm_HeymanStidham_HLG_Supplement_theorem_5
-- name    : HeymanStidham.HLG.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T11:14:35.55793+00:00
-- url     : https://prove2.me/theorems/2880aee1-41c2-4792-b790-26d9e3853e4f
-- title:
--   THEOREM 5 (companion theorem; not used in the proof of the goal) — regenerative ensemble relation
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space carrying arrival epochs $0\le t_1\le t_2\le\cdots$, customer functions $f_n$ on nonnegative time, and nonnegative spans $s_n$. Let $g_n=\int_0^\infty f_n(u)\,du$, $h(u)=\sum_n f_n(u)$, and $N(T)$ count the arrivals by time $T$. For almost every path assume (i) support in $[t_n,t_n+s_n]$, (ii) $s_n/n\to0$, and integrability of each customer function. Retain the inherited positive finite pathwise arrival rate and either the nonnegative finite-customer-average case of Theorem 1 or the finite positive/negative customer-average case of Theorem 2.
--
--   The interarrival sequence $\tau_n$ and the customer-total sequence $g_n$ are each regenerative with finite mean complete-cycle lengths, as in (viii) and (ix). Their epochs may be unrelated and the two sequences may be dependent. No integrability of cycle rewards is assumed in the regeneration definition.
--
--   Then there are a deterministic constant $0<\lambda<\infty$ and integrable real random variables $G(\omega)$ and $H(\omega)$ such that almost surely
--
--   $$\frac{N(\omega,T)}{T}\longrightarrow\lambda,\qquad
--   \frac1N\sum_{n=1}^N g_n(\omega)\longrightarrow G(\omega),\qquad
--   \frac1T\int_0^T h(\omega,u)\,du\longrightarrow H(\omega),\qquad
--   H(\omega)=\lambda G(\omega).$$
--
--   In particular the ensemble averages satisfy
--
--   $$\int_\Omega H(\omega)\,dP=\lambda\int_\Omega G(\omega)\,dP.\tag{8}$$
--
--   The time-average assertion includes integrability of $h$ on every bounded nonnegative time interval. This is a companion theorem extending the base pathwise relation to ensemble averages, and is not used to prove the goal.
--
--   **Formalization Note** The customer functions themselves may have both signs. Their integrated positive and negative parts are not assumed stationary or regenerative. The constant rate is concluded, not assumed. The finite inherited limit domain is retained literally, and the integrability of the ensemble limits is part of the conclusion.
--
--   Differences from the source:
--   - reading: Conditions are added to the hypotheses of Theorems 1 and 2. → InheritedPath retains a positive finite pathwise arrival-rate limit and either the nonnegative finite-average case or the signed finite-positive/negative-average case.; reason: The source and structured brief retain these existence and finiteness qualifications; some existence conclusions consequently overlap inherited hypotheses.
--   - encoding: Customers are numbered from one and all sample-path limit statements hold with probability one. → Customer n represents source customer n+1; the path domain and all pathwise conclusions are almost sure; only nonnegative-time values of the customer functions are constrained.; reason: This uses the published pathwise definitions and the standing convention on p. 984, without excluding tied arrivals.
--   - reading: The ensemble averages are the integrals of the pathwise limits. → The existential limit functions G and H are integrable and their real expectations obey equation (8).; reason: This keeps the ensemble integrals genuine rather than invoking the Bochner default on a nonintegrable function; no premise asserting integrability of the unknown limit is added.
--   - reading: (viii) and (ix) require regenerative sequences with finite mean times between regenerations. → Each sequence has its own delayed iid complete-block regeneration with integrable complete-cycle length.; reason: This is the classical regenerative-sequence meaning cited to Çinlar Chapter 9; no common epochs, cross-sequence independence or cycle-reward moment is required. The inherited finite-average requirements remain separate.
--   - reading: The source prints (iv) as ∫₀^∞ fₙ dt ≤ ∞, uses finite absolute integrals in (v), and defines H through finite-time integrals. → The inherited interface uses IntegrableOn for each customer function and includes interval integrability at every nonnegative horizon in IsTimeAverage.; reason: The published base interface repairs the (iv) finiteness typo consistently with finite gₙ and the proof; the well-definedness convention on p. 984 and the finite prefix integrals on p. 987 support genuine integrals. No negative-time regularity is imposed.
-- source:
--   Heyman and Stidham, The relation between customer and time averages in queues, Oper. Res. 28 (1980), DOI 10.1287/opre.28.4.983, p. 988, THEOREM 5 and (8); PDF p. 6

import Mathlib
import Definitions.Def_HeymanStidham_HLG_Setting
import Definitions.Def_HeymanStidham_HLG_Supplement_Regenerative
import Definitions.Def_HeymanStidham_HLG_Supplement_Lift
import Definitions.Def_HeymanStidham_HLG_Supplement_Ensemble

namespace HeymanStidham.HLG.Supplement

open MeasureTheory

/-- THEOREM 5, p. 988: the regenerative companion in both inherited domains.
The two sequences may have unrelated regeneration epochs and be dependent.
The inherited finite-limit conditions are not replaced by a reward moment. -/
theorem theorem_5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (t : Ω → ℕ → ℝ) (f : Ω → ℕ → ℝ → ℝ) (s : Ω → ℕ → ℝ)
    (hpath : ∀ᵐ ω ∂P, InheritedPath (t ω) (f ω) (s ω))
    (hviii : IsRegenerative (fun n ω => interarrival (t ω) n) P)
    (hix : IsRegenerative (fun n ω => custTotal (f ω) n) P) :
    ∃ (lam : ℝ) (G H : Ω → ℝ), 0 < lam ∧
      Integrable G P ∧ Integrable H P ∧
      (∀ᵐ ω ∂P, IsArrivalRate (t ω) lam ∧
        IsCustomerAverage (custTotal (f ω)) (G ω) ∧
        IsTimeAverage (rate (f ω)) (H ω) ∧ H ω = lam * G ω) ∧
      ensembleAverage P H = lam * ensembleAverage P G := by sorry

end HeymanStidham.HLG.Supplement
