-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_lemma_2
-- name    : ManyServerQED.Scheduling.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:46:53.065983+00:00
-- url     : https://prove2.me/theorems/9d4f959a-9f3b-40ee-acf1-a633abda2acd
-- title:
--   Lemma 2 — moment bound $E(\|\hat A^n\|^*_t)^{m_U}\le c(1+t^{m_U/2})$ for the scaled arrival processes
-- statement:
--   Under Assumption 3 (and the standing Assumption 1(i) of the model), there is a constant $c$, independent of $n$ and $t$, such that the scaled arrival processes $\hat A^n_i(t)=n^{-1/2}(A^n_i(t)-\lambda^n_it)$ satisfy
--   $$
--   E\big(\|\hat A^n\|^*_t\big)^{m_U}\le c\,(1+t^{m_U/2}),\qquad n\in\mathbb N,\ t\ge0,
--   $$
--   where $\|\hat A^n\|^*_t=\sup_{0\le s\le t}\|\hat A^n(s)\|$.
--
--   This bound controls the arrival part of the noise $\hat W^n$ in the moment estimate of Lemma 3.
--
--   **Formalization Note** The supremum and the expectation are computed in $[0,\infty]$ (the published `supDist` of the path to $0$), so the bound also asserts finiteness. Lemma 2 says "Under Assumption 3", but its proof uses $\sup_n\lambda^n_i/(n\lambda_i)<\infty$ from Assumption 1(i); that assumption is part of the model structure. $\mathbb N=\{1,2,\dots\}$.
-- source:
--   Atar, Mandelbaum & Reiman, Scheduling a Multi Class Queue with Many Exponential Servers: Asymptotic Optimality in Heavy Traffic, arXiv:math/0407058v1 (reprint of Ann. Appl. Probab. 14(3), 2004), p. 31, Lemma 2

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_ManyServerQED_Scheduling_Diffusion
import Definitions.Def_ManyServerQED_Scheduling_Model
import Definitions.Def_ManyServerQED_Scheduling_Policy

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ManyServerQED.Scheduling

open BellWilliams2001.ThresholdPolicy

/-- Lemma 2 (p. 31): under Assumption 3 (and the standing Assumption 1(i)),
`E(‖Âⁿ‖*_t)^{m_U} ≤ c(1 + t^{m_U/2})` for all `n ≥ 1` and `t ≥ 0`, with `c` independent of `n` and
`t`; `‖Âⁿ‖*_t = sup_{0 ≤ s ≤ t} ‖Âⁿ(s)‖` (ℓ¹ norm). -/
theorem lemma_2 {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (M : SystemSequence Ω k) (mL mU : ℝ)
    (hA3 : M.Assumption3 mL mU) :
    ∃ c : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ t : ℝ, 0 ≤ t →
      ∫⁻ ω, supDist (M.Ahat n ω) (fun _ => 0) t ^ mU ∂M.P ≤
        ENNReal.ofReal (c * (1 + t ^ (mU / 2))) := by sorry

end ManyServerQED.Scheduling
