-- Prove2me | Theorems.Thm_KleywegtSAA_ValueCLT_scaled_gap_tendsto_zero
-- name    : KleywegtSAA.ValueCLT.scaled_gap_tendsto_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:09:19.655495+00:00
-- url     : https://prove2.me/theorems/73a7a065-2525-44d9-8f0a-97bc43dce20e
-- title:
--   §2.2, (2.6), p. 5 — √N[v̂_N − min_{x∈𝒮*} ĝ_N(x)] → 0 w.p.1 and in probability
-- statement:
--   Under the setting of (1.1)–(2.1) (a nonempty finite feasible set $\mathcal S$, an integrand $G(x, \cdot)$ that is measurable and integrable for every $x \in \mathcal S$, and an i.i.d. sample $W^1, W^2, \dots$), let $\hat v_N$ be the SAA optimal value and $\mathcal S^*$ the set of optimal solutions of the true problem. Then
--   $$\lim_{N \to \infty} \sqrt N \Big[\hat v_N - \min_{x \in \mathcal S^*} \hat g_N(x)\Big] = 0 \quad \text{w.p.1}, \tag{2.6}$$
--   and consequently $\sqrt N\,[\hat v_N - \min_{x \in \mathcal S^*} \hat g_N(x)]$ converges to $0$ in probability, i.e.
--   $$\hat v_N = \min_{x \in \mathcal S^*} \hat g_N(x) + o_p(N^{-1/2}).$$
--
--   It reduces the asymptotic distribution of $\hat v_N$ to that of the minimum of the sample averages over the true optimal set.
--
--   **Formalization Note** The statement is the conjunction of almost sure convergence and convergence in measure (Mathlib's `TendstoInMeasure`) to the constant $0$; the $o_p(N^{-1/2})$ notation is not introduced.
-- source:
--   Kleywegt & Shapiro, The sample average approximation method for stochastic discrete optimization, preprint (two-author version, sha256 56657748…), p. 5, §2.2, proof of Proposition 2.3, (2.6) and the o_p(N^{−1/2}) display

import Mathlib
import Definitions.Def_KleywegtSAA_ValueCLT_Setting

namespace KleywegtSAA.ValueCLT

open MeasureTheory ProbabilityTheory Filter Topology

/-- Kleywegt–Shapiro, §2.2, (2.6), p. 5: `√N [v̂_N − min_{x ∈ S*} ĝ_N(x)] → 0` with probability one,
and hence in probability, i.e. `v̂_N = min_{x ∈ S*} ĝ_N(x) + o_p(N^{-1/2})`. -/
theorem scaled_gap_tendsto_zero
    {X : Type*} (S : Finset X) (hS : S.Nonempty)
    {𝒲 : Type*} [MeasurableSpace 𝒲] (G : X → 𝒲 → ℝ) (hG : ∀ x ∈ S, Measurable (G x))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℕ → Ω → 𝒲) (hWm : ∀ n, Measurable (W n)) (hind : iIndepFun W P)
    (hid : ∀ n, IdentDistrib (W n) (W 0) P P)
    (hint : ∀ x ∈ S, Integrable (fun ω => G x (W 0 ω)) P) :
    (∀ᵐ ω ∂P, Tendsto (fun N : ℕ =>
        Real.sqrt N * (S.inf' hS (KleywegtSAA.ExpRate.sampleObj G W N ω) - minOnOpt S hS G P W N ω)) atTop (𝓝 0)) ∧
    TendstoInMeasure P (fun (N : ℕ) ω =>
        Real.sqrt N * (S.inf' hS (KleywegtSAA.ExpRate.sampleObj G W N ω) - minOnOpt S hS G P W N ω))
      atTop (fun _ => 0) := by sorry

end KleywegtSAA.ValueCLT
