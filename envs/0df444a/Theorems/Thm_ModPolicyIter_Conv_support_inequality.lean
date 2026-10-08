-- Prove2me | Theorems.Thm_ModPolicyIter_Conv_support_inequality
-- name    : ModPolicyIter.Conv.support_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:33:38.527266+00:00
-- url     : https://prove2.me/theorems/3da4d27e-d199-4bf0-833c-cbed4b93524c
-- title:
--   (7), p. 1131 — support inequality Bw ≥ Bv + (λP_v − I)(w − v)
-- statement:
--   Let $S$ be a set of states with a $\sigma$-algebra. Each policy $P\in\mathcal P$ is a Markov transition kernel on $S$ with a measurable one-period reward $c_P$, where $\sup_P\sup_s|c_P(s)|\le M$ and $0\le\lambda<1$. Let $V$ be the space of bounded measurable functions with $\|v\|=\sup_s|v(s)|$.
--
--   Let $v,w\in V$ and let $P_v$ attain the maximum in (1) at $v$. Then, pointwise on $S$,
--
--   $$Bw\ \ge\ Bv+(\lambda P_v-I)(w-v).$$
--
--   This **support inequality**, due to Puterman and Brumelle and quoted in the proof of Lemma 4, says that the convex operator $B$ lies above its "tangent" $\lambda P_v-I$ at $v$; it is what makes policy iteration a Newton method, and it drives Lemma 4 and the rate bound (9).
--
--   **Formalization Note** The attainment of the maximum is needed only at $v$ and is given as the hypothesis that the policy $P_v$ is a maximizer there; the standing assumption for all $v$ is not used.
-- source:
--   Puterman and Shin, Modified policy iteration algorithms for discounted Markov decision problems, Management Science 24 (1978), DOI 10.1287/mnsc.24.11.1127, p. 1131, (7) in the proof of Lemma 4 (Puterman–Brumelle, Proposition 1)

import Mathlib
import Definitions.Def_ModPolicyIter_Conv_Model

open MeasureTheory ProbabilityTheory

namespace ModPolicyIter.Conv

/-- The support inequality (7) (Puterman–Shin 1978, proof of Lemma 4, p. 1131, quoting
Puterman–Brumelle, Proposition 1): for `v, w ∈ V` and a maximizer `P_v` at `v`,
`Bw ≥ Bv + (λP_v − I)(w − v)`. -/
theorem support_inequality {S : Type*} [MeasurableSpace S] {ι : Type*} (m : Model S ι) :
    ∀ v w : S → ℝ, IsBM v → IsBM w → ∀ i, Attains m v i →
      ∀ s, B m v s + (m.lam * Pop m i (w - v) s - (w - v) s) ≤ B m w s := by sorry

end ModPolicyIter.Conv
