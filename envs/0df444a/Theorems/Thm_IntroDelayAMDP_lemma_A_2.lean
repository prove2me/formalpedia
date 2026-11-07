-- Prove2me | Theorems.Thm_IntroDelayAMDP_lemma_A_2
-- name    : IntroDelayAMDP.lemma_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:46:10.848438+00:00
-- url     : https://prove2.me/theorems/9122465c-3acf-450c-877e-efc98abd8db9
-- title:
--   Lemma A.2 — parameters for tabular AMDPs
-- statement:
--   For $C$ large enough, all $S,A,H,K\ge1$, $\delta\in(0,1)$ and every $\bar d\le K$, the parameters of App. A.1 satisfy:
--
--   1. (P1) $\theta\le1/C$ and $c_1\eta H^3\le H\theta$;
--   2. (P2) $(M+2\bar d)\eta H^2(\nu+2H)\le1/2$;
--   3. (P3) $\log_2(2/\theta)\le\iota$.
--
--   These inequalities are the deterministic facts about the parameters that every later lemma uses.
--
--   Differences from the source:
--   - reading: C a large enough universal constant → ∃ C₀, ∀ C ≥ C₀; reason: the strong reading of "large enough" (p.30)
--   - reading: d̄ is 0 for Algorithm 1 and 1 ≤ d̄ ≤ K in Appendix C → every d̄ ≤ K; reason: covers both cases as printed
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Lemma A.2, p.30

import Mathlib
import Definitions.Def_IntroDelayAMDP_tabParams

namespace IntroDelayAMDP

open MeasureTheory

/-- **Lemma A.2 (Parameters for Tabular AMDPs)** (printed p.30, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)): "The parameters above satisfy
the following: (P1) `θ ≤ 1/C` and `c₁ηH³ ≤ Hθ`; (P2) `(M + 2d̄)ηH²(ν + 2H) ≤ 1/2`; (P3) `log₂(2/θ) ≤ ι`."

For `C` large enough, all `S, A, H, K ≥ 1`, `δ ∈ (0, 1)` and every delay cap `d̄ ≤ K` (`d̄ = 0` for
Algorithm 1, `1 ≤ d̄ ≤ K` in Appendix C), the parameters `tabParams C d̄ S A H K δ` satisfy (P1)–(P3). -/
theorem lemma_A_2 :
    ∃ C₀ : ℝ, ∀ C ≥ C₀, ∀ S A H K dbar : ℕ, 1 ≤ S → 1 ≤ A → 1 ≤ H → 1 ≤ K → dbar ≤ K →
      ∀ δ : ℝ, 0 < δ → δ < 1 →
      let p := tabParams C dbar S A H K δ
      (p.theta ≤ 1 / C ∧ p.c1 * p.eta * (H : ℝ) ^ 3 ≤ (H : ℝ) * p.theta) ∧
        ((p.M : ℝ) + 2 * dbar) * p.eta * (H : ℝ) ^ 2 * (p.nu + 2 * H) ≤ 1 / 2 ∧
        Real.logb 2 (2 / p.theta) ≤ p.iota := by sorry

end IntroDelayAMDP
