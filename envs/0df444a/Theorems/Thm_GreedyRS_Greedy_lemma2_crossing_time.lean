-- Prove2me | Theorems.Thm_GreedyRS_Greedy_lemma2_crossing_time
-- name    : GreedyRS.Greedy.lemma2_crossing_time
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:11:59.771836+00:00
-- url     : https://prove2.me/theorems/70198966-5b7a-489c-9c3f-ef718d2f617a
-- title:
--   Lemma 2, pp. 13–14 — law of Ñ(x): E[Ñ(x)] = exp(Σ Φ(−√n x)/n) for x > 0; Pr{Ñ(x) < ∞} = 1 − exp(−Σ Φ(√n x)/n) for x < 0
-- statement:
--   Let $Z_1,Z_2,\dots$ be i.i.d. $N(0,1)$, $\bar Z(n)=\frac1n\sum_{j=1}^nZ_j$, and let $\tilde N(x)=\inf\{n\ge1:\bar Z(n)<x\}$ be the first time the running average drops below $x$ ($\tilde N(x)=\infty$ if it never does). Let $\Phi$ be the standard normal distribution function.
--
--   1. For every $x>0$, $\Pr\{\tilde N(x)<\infty\}=1$ and
--   $$\mathrm E\bigl[\tilde N(x)\bigr]=\exp\Bigl(\sum_{n=1}^\infty\frac1n\Phi(-\sqrt n\,x)\Bigr);\qquad(4.1)$$
--   moreover $x\mapsto\mathrm E[\tilde N(x)]$ is continuous and strictly decreasing on $(0,\infty)$.
--   2. For every $x<0$, $\mathrm E[\tilde N(x)]=\infty$ and
--   $$\Pr\{\tilde N(x)<\infty\}=1-\exp\Bigl(-\sum_{n=1}^\infty\frac1n\Phi(\sqrt n\,x)\Bigr);\qquad(4.2)$$
--   moreover $x\mapsto\Pr\{\tilde N(x)<\infty\}$ is continuous and strictly increasing on $(-\infty,0)$.
--   3. For $x=0$, $\Pr\{\tilde N(0)<\infty\}=1$ and $\mathrm E[\tilde N(0)]=\infty$.
--
--   These are Spitzer-type identities for the Gaussian random walk $\sum_j(Z_j-x)$. Part 1 gives the closed form $C(x)$ of the expected boundary-crossing time used throughout the paper, and its continuity and monotonicity are what make the constant $\gamma_0$ of Theorem 1 well defined.
--
--   **Formalization Note** $\tilde N(x)$ is valued in $\mathbb N\cup\{\infty\}$ and its expectation is a lower Lebesgue integral in $[0,\infty]$, so "$=\infty$" is literal and continuity is in the topology of $[0,\infty]$. Probabilities are in $[0,\infty]$. The sums are written with $n+1$ in place of $n$, starting from $0$.
-- source:
--   Li, Fan & Hong, The (Surprising) Sample Optimality of Greedy Procedures for Large-Scale Ranking and Selection, arXiv:2303.02951v3, pp. 13–14, Lemma 2, (4.1), (4.2); proof EC.1.2, pp. ec1–ec2, and Siegmund (1985), Corollaries 8.39, 8.44

import Mathlib
import Definitions.Def_GreedyRS_Greedy_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GreedyRS.Greedy
theorem lemma2_crossing_time :
    -- x > 0: finiteness and (4.1)
    (∀ x : ℝ, 0 < x →
      stdNormalSeq {z | crossTime x 1 z < ⊤} = 1 ∧ Cn0 x 1 = ENNReal.ofReal (Cfun x)) ∧
    StrictAntiOn (fun x => Cn0 x 1) (Set.Ioi 0) ∧
    ContinuousOn (fun x => Cn0 x 1) (Set.Ioi 0) ∧
    -- x < 0: infinite mean and (4.2)
    (∀ x : ℝ, x < 0 →
      Cn0 x 1 = ⊤ ∧
      stdNormalSeq {z | crossTime x 1 z < ⊤} =
        ENNReal.ofReal (1 - Real.exp (-∑' n : ℕ,
          Phi (Real.sqrt ((n : ℝ) + 1) * x) / ((n : ℝ) + 1)))) ∧
    StrictMonoOn (fun x => stdNormalSeq {z | crossTime x 1 z < ⊤}) (Set.Iio 0) ∧
    ContinuousOn (fun x => stdNormalSeq {z | crossTime x 1 z < ⊤}) (Set.Iio 0) ∧
    -- x = 0
    stdNormalSeq {z | crossTime 0 1 z < ⊤} = 1 ∧ Cn0 0 1 = ⊤ := by sorry
end GreedyRS.Greedy
