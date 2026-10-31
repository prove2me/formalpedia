-- Prove2me | Theorems.Thm_LearnManip_lemma_3
-- name    : LearnManip.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:02:44.938282+00:00
-- url     : https://prove2.me/theorems/280deb87-bbc1-47db-a0c9-70de30c9f758
-- title:
--   Lemma 3, p.33 (corrected: $0<\eta$ in (a), (c); (a) one-sided; (d) off the thresholds) — derivatives of $G$
-- statement:
--   Let $0\le\eta\le1$, $c>0$, and let $G$ be the closed form (18). Then $G(\cdot,c)$ is differentiable at every $s>0$, and:
--
--   1. if $\eta>0$, its right derivative at $s=0$ is $0$;
--   2. $\lim_{s\to\infty}\partial_sG(s,c)=\dfrac{1}{2\gamma(1-\alpha)^2}$;
--   3. if $\eta>0$, there is $\hat s\ge0$ such that $\partial_sG(s,c)=0$ on $(0,\hat s]$ and $\partial_sG$ is strictly increasing on $[\hat s,\infty)\cap(0,\infty)$;
--   4. at every $s>0$ different from all thresholds $s_{TH}(c\eta^j)$, the second derivative exists and
--   $$\partial^2_sG(s,c)\le\frac{2c}{s^3}.$$
--
--   The paper's proof of Theorem 1 rests on these properties through the first-order condition of (15).
--
--   Differences from the source:
--   - correction: (a) and (c) for c, γ > 0 and η ≤ 1 → (a) and (c) for 0 < η ≤ 1, the other clauses for every η ≤ 1; reason: at η = 0, α = 1/2, G(s, c) = αKs on [0, s_TH(c)], so ∂_sG is a positive constant there and (a), (c) fail
--   - correction: (d) ∂²_sG exists and is at most 2c/s³ on [0, ∞) → at every s > 0 off the thresholds s_TH(cη^j); reason: at α = 0, η = 1, γ = 1/2, c = 1, G(s, 1) = (s−1)²/s for s > 1 and 0 for s ≤ 1, so G″ jumps at s = 1
--   - reading: (a) ∂_sG(0, c) = 0 → a right derivative at 0; reason: G is defined on [0, ∞)
--   - encoding: G, the solution of (15) → the closed form (18); reason: the milestone Theorem 1 identifies them; the function of a real variable sends negative reals to 0, and only s ≥ 0 is used
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), Lemma 3, p.33; proof, pp.ec10–ec11 (PDF 49–50)

import Mathlib
import Definitions.Def_LearnManip_Params
import Definitions.Def_LearnManip_sTH
import Definitions.Def_LearnManip_coeffK
import Definitions.Def_LearnManip_GclosedReal

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory InformationTheory Filter

namespace LearnManip

/-- Lemma 3, p.33, of Keppo, Kim, Zhang (SSRN 3465030, 2021-09-04), **corrected**, for `G` the closed
form (18), `η ≤ 1`, `c > 0`: `G` is differentiable at every `s > 0`; (a) for `η > 0`, its right
derivative at `0` is `0`; (b) `∂_s G → 1/(2γ(1−α)²)`; (c) for `η > 0`, there is `ŝ ≥ 0` with `∂_s G = 0`
on `(0, ŝ]`, strictly increasing on `[ŝ, ∞) ∩ (0, ∞)`; (d) off the thresholds `s_TH(c η^j)`, `∂²_s G`
exists and is at most `2c/s³`.

**Formalization Note.** As printed the lemma is false: `G″` jumps at the thresholds (at `α = 0`, `η = 1`,
`γ = 1/2`, `c = 1`), and (a), (c) fail at `η = 0` (at `α = 1/2`, `G = αKs` near `0`). Only (a) and (c)
carry `0 < η`; the differentiability, (b) and (d) are kept for every `η ≤ 1`, `η = 0` included. -/
theorem lemma_3 (P : Params) (hη₁ : P.η ≤ 1) {c : ℝ≥0} (hc : 0 < c) :
    (∀ s : ℝ, 0 < s → DifferentiableAt ℝ (GclosedReal P c) s) ∧
    (0 < P.η → HasDerivWithinAt (GclosedReal P c) 0 (Set.Ici 0) 0) ∧
    Tendsto (deriv (GclosedReal P c)) atTop (𝓝 (coeffK P)) ∧
    (0 < P.η → ∃ ŝ : ℝ, 0 ≤ ŝ ∧ (∀ s : ℝ, 0 < s → s ≤ ŝ → deriv (GclosedReal P c) s = 0) ∧
      StrictMonoOn (deriv (GclosedReal P c)) (Set.Ici ŝ ∩ Set.Ioi 0)) ∧
    ∀ s : ℝ, 0 < s → (∀ j : ℕ, s ≠ (sTH P (c * P.η ^ j) : ℝ)) →
      DifferentiableAt ℝ (deriv (GclosedReal P c)) s ∧
        deriv (deriv (GclosedReal P c)) s ≤ 2 * (c : ℝ) / s ^ 3 := by sorry

end LearnManip
