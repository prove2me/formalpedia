-- Prove2me | Theorems.Thm_KLZ97_network_failure_le_card_mul
-- name    : KLZ97.network_failure_le_card_mul
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T12:55:41.731335+00:00
-- url     : https://prove2.me/theorems/675acf43-3dcb-4ece-86a5-57fe6ec54346
-- title:
--   Network failure bound in the quasi-independent stochastic model: $\le n p$
-- statement:
--   The paper's bound on the probability that a network's computation fails. A network with $n$ error locations obeying the quasi-independent stochastic error model with error probability $p$ fails — meaning that at least one error location carries a non-identity operator — with probability at most $n p$. This is the estimate behind the remark that high probability of success is assured as soon as $p \ll 1/n$.
-- source:
--   Knill, Laflamme, Zurek, Resilient Quantum Computation: Error Models and Thresholds, arXiv:quant-ph/9702058v1, https://arxiv.org/abs/quant-ph/9702058, Section I.B (Assumptions and error models), p. 4

import Mathlib
import Definitions.Def_KLZ97_model

namespace KLZ97

theorem network_failure_le_card_mul {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (locs : Finset ι) (fail : ι → Set Ω) (p : ENNReal)
    (hmodel : QuasiIndepStochastic μ locs fail p) :
    μ (⋃ i ∈ locs, fail i) ≤ locs.card * p := by sorry

end KLZ97
