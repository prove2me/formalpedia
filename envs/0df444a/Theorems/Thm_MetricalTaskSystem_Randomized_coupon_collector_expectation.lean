-- Prove2me | Theorems.Thm_MetricalTaskSystem_Randomized_coupon_collector_expectation
-- name    : MetricalTaskSystem.Randomized.coupon_collector_expectation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T19:20:30.147831+00:00
-- url     : https://prove2.me/theorems/5f408fbf-9eb5-4eb6-8af4-2b1fdcc23be6
-- title:
--   Section 7, lower bound — the coupon-collector expectation $nH(n)$
-- statement:
--   Let $S$ be a set of $n\ge 1$ states and let $\omega_0,\omega_1,\dots$ be independent, each uniformly distributed on $S$. Let $Y$ be the least $k$ such that $\omega_0,\dots,\omega_{k-1}$ contains every state of $S$ ($Y=\infty$ if there is none). Then
--   $$E(Y)=nH(n)=n\Big(1+\frac12+\cdots+\frac1n\Big).$$
--
--   In the paper this computes the mean length of a renewal cycle of the off-line strategy, which gives the off-line cost rate $1/(nH(n))$.
--
--   **Formalization Note** $Y$ is valued in $[0,\infty]$ and $E(Y)$ is a lower Lebesgue integral, so no integrability hypothesis is involved. The law of the sequence is `Measure.infinitePi` of the uniform distribution on $S$.
-- source:
--   Borodin, Linial, Saks, An Optimal On-Line Algorithm for Metrical Task System, J. ACM 39(4) (1992), p. 760, Section 7, proof of Theorem 7.1 (lower bound), computation of Exp(Y_k)

import Mathlib
import Definitions.Def_MetricalTaskSystem_Randomized_Model
import Definitions.Def_MetricalTaskSystem_Randomized_TaskDistribution

namespace MetricalTaskSystem.Randomized

open MeasureTheory

/-- **Section 7, proof of the lower bound, coupon collector** (Borodin–Linial–Saks 1992,
p. 760). For a sequence of independent states, each uniform on the `n`-element set `S`, the
expected number of states until every state has appeared is `n·H(n)`. -/
theorem coupon_collector_expectation {S : Type} [Fintype S] [Nonempty S]
    [MeasurableSpace S] [MeasurableSingletonClass S] :
    ∫⁻ ω, collectTime ω ∂(uniformStateSeq S) =
      ENNReal.ofReal ((Fintype.card S : ℝ) * (harmonic (Fintype.card S) : ℝ)) := by sorry

end MetricalTaskSystem.Randomized
