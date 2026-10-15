-- Prove2me | Theorems.Thm_FreeSamples_Revenue_lemma_3
-- name    : FreeSamples.Revenue.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:42:01.222305+00:00
-- url     : https://prove2.me/theorems/91704083-9375-4a1b-ae57-aa43144ddd89
-- title:
--   Lemma 3, p. 16 — at the stopping amount, selling the whole remainder at price BR(θ_T, σ_T²) is optimal
-- statement:
--   Let $u$ satisfy the HasMax hypothesis, and consider a Buyer with belief $\mathcal N(m,v)$, $v>0$. For a signal $y\sim\mathcal N(\theta,s)$ of noise variance $s\ge 0$, the most the Buyer pays is
--   $$p(m,v;s)=\mathbb E_{y\sim\mathcal N(m,v+s)}\Big[U\Big(\tfrac{sm+vy}{v+s},\tfrac{vs}{v+s}\Big)\Big]-U(m,v),$$
--   her expected optimal utility after the signal minus her optimal utility now. Then:
--
--   1. releasing the whole remaining dataset ($s=0$, the Buyer learns $\theta$) is worth exactly the Bayes risk, $p(m,v;0)=BR(m,v)$;
--   2. every partial release is worth at most that: for every $s>0$ for which the post-signal utility $y\mapsto U(\cdot)$ is integrable, $p(m,v;s)\le BR(m,v)$.
--
--   Applied at the stopping state $(m,v)=(\theta_T,\sigma_T^2)$, this is Lemma 3. When the free samples stop, the Seller's best move is to sell the remainder of the dataset at the price $BR(\theta_T,\sigma_T^2)$. This fixes the revenue of every free-sample policy as $\mathbb E^S_0[BR(\theta_T,\sigma_T^2)]$.
--
--   **Formalization Note.** The lemma is stated statically at the stopping state, using the explicit Gaussian posterior after one signal (the one-signal analogue of Proposition 1) as an encoding. The integrability of the post-signal utility for $s>0$ is a disclosed hypothesis; it excludes Lean's junk value $0$ for a non-integrable integral.
-- source:
--   Drakopoulos & Makhdoumi, Providing Data Samples for Free, SSRN 3611003, p. 16, Lemma 3; proof p. 30

import Mathlib
import Definitions.Def_FreeSamples_Revenue_Setting

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace FreeSamples.Revenue

theorem lemma_3 (u : ℝ → ℝ → ℝ) (hu : HasMax u) (m v : ℝ) (hv : 0 < v) :
    signalPrice u m v 0 = BR u m v ∧
    ∀ s : ℝ, 0 < s →
      Integrable (fun y => Uval u (sigPostMean m v s y) (sigPostVar v s)) (N m (v + s)) →
      signalPrice u m v s ≤ BR u m v := by sorry

end FreeSamples.Revenue
