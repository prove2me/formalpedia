-- Prove2me | Theorems.Thm_IntermediateDisorder_PointToLine_modifiedPartitionFunction_eq_sum_uStatistic
-- name    : IntermediateDisorder.PointToLine.modifiedPartitionFunction_eq_sum_uStatistic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:42:43.653458+00:00
-- url     : https://prove2.me/theorems/bfa19efb-f35e-4e8c-a192-00baf6a72cd3
-- title:
--   Lemma 5.2 — $\mathfrak z_n^\omega(\beta)=\sum_{k=0}^n2^{k/2}\beta^k\mathcal S_k^n(p_k^n)$
-- statement:
--   Let the environment be i.i.d. with mean zero and variance one, let $n\ge1$ and $\beta\in\mathbb R$. Then, with probability one, the modified point-to-line partition function can be rewritten as
--
--   $$\mathfrak z_n^\omega(\beta)=\sum_{k=0}^n2^{k/2}\beta^k\,\mathcal S_k^n(p_k^n)=\sum_{k=0}^n2^{k/2}\beta^kn^{-k/2}\,\mathcal S_k^n\big(n^{k/2}p_k^n\big).$$
--
--   Consequently,
--
--   $$\mathfrak z_n^\omega(\beta n^{-1/4})=\sum_{k=0}^n2^{k/2}\beta^kn^{-3k/4}\,\mathcal S_k^n\big(n^{k/2}p_k^n\big).$$
--
--   This identity puts the modified partition function in the form of a discrete chaos, to which Lemma 4.4 applies once $n^{k/2}p_k^n$ is compared with $\varrho_k$.
--
--   **Formalization Note** $\mathcal S_k^n$ is an $L^2(Q)$-valued object, so the identity is an equality almost surely (it in fact holds for every environment, every sum being finite). The $k=0$ term is $1$ ($p_0^n=1$, $\mathcal S_0^n(g_0)=g_0$). The powers $n^{-k/2}$, $n^{-3k/4}$, $n^{-1/4}$ are real powers, which is why $n\ge1$ is assumed.
-- source:
--   Alberts, Khanin, Quastel, The intermediate disorder regime for directed polymers in dimension 1+1, arXiv:1202.4398v3, p. 30, Lemma 5.2

import Mathlib
import Definitions.Def_IntermediateDisorder_PointToLine_Environment
import Definitions.Def_IntermediateDisorder_PointToLine_WienerChaos
import Definitions.Def_IntermediateDisorder_PointToLine_UStatistic

namespace IntermediateDisorder.PointToLine

open MeasureTheory ProbabilityTheory

/-- Lemma 5.2: for `n ≥ 1` and `β ∈ ℝ`, almost surely
`𝔷_n^ω(β) = ∑_{k=0}^n 2^{k/2} β^k 𝒮_k^n(p_k^n) = ∑_{k=0}^n 2^{k/2} β^k n^{-k/2} 𝒮_k^n(n^{k/2} p_k^n)`,
and consequently `𝔷_n^ω(βn^{-1/4}) = ∑_{k=0}^n 2^{k/2} β^k n^{-3k/4} 𝒮_k^n(n^{k/2} p_k^n)`. -/
theorem modifiedPartitionFunction_eq_sum_uStatistic {Ω : Type*} [MeasurableSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q] {ω : ℕ × ℤ → Ω → ℝ}
    (hω : IsStdEnvironment ω Q) (n : ℕ) (hn : 1 ≤ n) (β : ℝ) :
    (modifiedPartitionFunction ω n β =ᵐ[Q]
      ((∑ k ∈ Finset.range (n + 1),
        (Real.sqrt 2 ^ k * β ^ k) • uStatistic ω Q n k (discreteKernelLp n k) : Lp ℝ 2 Q) :
          Ω → ℝ)) ∧
    (modifiedPartitionFunction ω n β =ᵐ[Q]
      ((∑ k ∈ Finset.range (n + 1),
        (Real.sqrt 2 ^ k * β ^ k * (n : ℝ) ^ (-((k : ℝ) / 2))) •
          uStatistic ω Q n k ((n : ℝ) ^ ((k : ℝ) / 2) • discreteKernelLp n k) : Lp ℝ 2 Q) :
          Ω → ℝ)) ∧
    (modifiedPartitionFunction ω n (β * (n : ℝ) ^ (-(1 / 4 : ℝ))) =ᵐ[Q]
      ((∑ k ∈ Finset.range (n + 1),
        (Real.sqrt 2 ^ k * β ^ k * (n : ℝ) ^ (-(3 * (k : ℝ) / 4))) •
          uStatistic ω Q n k ((n : ℝ) ^ ((k : ℝ) / 2) • discreteKernelLp n k) : Lp ℝ 2 Q) :
          Ω → ℝ)) := by sorry

end IntermediateDisorder.PointToLine
