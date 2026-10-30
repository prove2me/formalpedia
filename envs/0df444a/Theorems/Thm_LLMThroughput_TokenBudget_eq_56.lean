-- Prove2me | Theorems.Thm_LLMThroughput_TokenBudget_eq_56
-- name    : LLMThroughput.TokenBudget.eq_56
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:40:37.766386+00:00
-- url     : https://prove2.me/theorems/6c1cf762-0926-481f-9706-a311fc7e9ff0
-- title:
--   Eq. (56), App. B.3, p. 41 — strong law of large numbers: E(n)/n → λ, V_p(N)/N → m_p, V_d(N)/N → m_d almost surely
-- statement:
--   **Strong law for arrivals and token sizes.** Work in the i.i.d. arrival model of §3.1. On a probability space $(\Omega,\mathcal F,\mathbb P)$ the following hold:
--
--   - the arrival counts $a_n$ are i.i.d. with $\lambda=E[a_1]<\infty$;
--   - the sizes $(v_p(i),v_d(i))$ are i.i.d. with $1\le v_p(i)\le v_p^{\max}$ and $1\le v_d(i)\le v_d^{\max}$;
--   - the two sequences are independent.
--
--   Let $m_p=E[v_p(1)]$ and $m_d=E[v_d(1)]$. Let $E(n)$ be the number of requests arrived in the first $n$ slots, and let $V_f(N)=\sum_{i\le N}v_f(i)$ for $f\in\{p,d\}$. Then
--   $$
--   \mathbb P\Big\{\omega:\ \lim_{n\to\infty}\tfrac1n E(n,\omega)=\lambda,\ \ \lim_{N\to\infty}\tfrac1N V_p(N,\omega)=m_p,\ \ \lim_{N\to\infty}\tfrac1N V_d(N,\omega)=m_d\Big\}=1 .
--   $$
--
--   These limits are the long-run arrival rates of requests and of prefill and decode work. The proof of Theorem 2(a) uses them, and so does the construction of fluid limits.
--
--   **Formalization Note** The first $n$ slots are slots $0,\dots,n-1$, and $V_f(N)$ sums requests $0,\dots,N-1$. At $n=0$ the quotient is Lean's $0/0=0$, which does not affect the limit. The random variables are measurable, and finiteness of $\lambda$ is integrability of $a_1$.
--
--   Differences from the source:
--   - encoding: two i.i.d. sequences $\{a_n\}$ and $\{(v_p(i),v_d(i))\}$, independent of each other, with $\lambda=E[a_1]$ → measurable maps, mutually independent (`iIndepFun`) and identically distributed (`IdentDistrib`) within each sequence, the two sequences independent as random elements of $\mathbb N^{\mathbb N}$ and $(\mathbb N^2)^{\mathbb N}$, and $a_1$ integrable; reason: the same assumptions in Lean's vocabulary. The paper's $\lambda$ is finite (p. 42, "the first moment assumption on $a_n$")
--   - encoding: $E(n)=\sum_{\ell=1}^n a_\ell$, $V_f(N)=\sum_{i=1}^N v_f(i)$ → sums over the 0-based indices $m<n$ and $i<N$; reason: Lean convention; same quantities
-- source:
--   Dai, Deng, Li & Peng, Throughput-Optimal Scheduling Algorithms for LLM Inference and AI Agents, arXiv:2504.07347v3, p. 41, eq. (56), App. B.3 (E(n), V_f(N) defined on p. 37, eq. (38); arrival model pp. 12–13)

import Mathlib
import Definitions.Def_LLMThroughput_TokenBudget_Model

namespace LLMThroughput.TokenBudget

open MeasureTheory ProbabilityTheory Filter Topology

theorem eq_56 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (vpmax vdmax : ℕ) (a : ℕ → Ω → ℕ) (v : ℕ → Ω → ℕ × ℕ)
    (hA : IIDArrivals μ a v vpmax vdmax) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => (arrivalsBefore (fun m => a m ω) n : ℝ) / n) atTop
          (𝓝 (arrivalRate μ a)) ∧
        Tendsto (fun N : ℕ => (∑ i ∈ Finset.range N, ((v i ω).1 : ℝ)) / N) atTop
          (𝓝 (meanPrefill μ v)) ∧
        Tendsto (fun N : ℕ => (∑ i ∈ Finset.range N, ((v i ω).2 : ℝ)) / N) atTop
          (𝓝 (meanDecode μ v)) := by sorry

end LLMThroughput.TokenBudget
