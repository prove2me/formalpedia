-- Prove2me | Theorems.Thm_KieferWolfowitz_Convergence_subseq_tendstoInMeasure
-- name    : KieferWolfowitz.Convergence.subseq_tendstoInMeasure
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:49:00.537268+00:00
-- url     : https://prove2.me/theorems/200deb6a-67ad-4a70-b2c4-7e971df0ad5f
-- title:
--   p. 465, after (3.19) — if $E\{K_{n_j}|z_{n_j}-\theta|\}\to0$ then $z_{n_j}\to\theta$ in probability
-- statement:
--   Let $M:\mathbb R\to\mathbb R$ satisfy Condition 3 about $\theta$: for every $\delta>0$ there is $\pi(\delta)>0$ with $|M(z+\varepsilon)-M(z-\varepsilon)|/\varepsilon>\pi(\delta)$ whenever $|z-\theta|>\delta$ and $0<\varepsilon<\delta/2$. Let $c_n>0$ with $c_n\to0$, let $z_n$ be real random variables on a probability space $(\Omega,P)$, and put $K_n=|(M(z_n+c_n)-M(z_n-c_n))/c_n|$. Let $n_1<n_2<\cdots$ be such that each $K_{n_j}|z_{n_j}-\theta|$ is integrable and
--   $$\lim_{j\to\infty}E\{K_{n_j}\,|z_{n_j}-\theta|\}=0. \tag{3.19}$$
--   Then $z_{n_j}-\theta$ converges stochastically to zero: for every $\delta>0$, $P\{|z_{n_j}-\theta|\ge\delta\}\to0$ as $j\to\infty$.
--
--   Applied with the subsequence supplied by (3.18), it gives a subsequence of the Kiefer–Wolfowitz iterates converging to $\theta$ in probability, from which the proof restarts.
--
--   **Formalization Note** Only Condition 3, $c_n>0$, $c_n\to0$ and integrability are used; the process structure is not needed and $z_n$ are arbitrary random variables. Integrability of $K_{n_j}|z_{n_j}-\theta|$ is a hypothesis, so (3.19) cannot hold by Lean's default value $0$ for a non-integrable function. Convergence in probability is Mathlib's `TendstoInMeasure` (with $\ge\delta$, equivalent to the paper's $>\delta$ over all $\delta>0$). The subsequence is a strictly increasing map $j\mapsto n_j$.
-- source:
--   Kiefer & Wolfowitz, Stochastic estimation of the maximum of a regression function, Ann. Math. Statist. 23 (1952), p. 465, (3.19) and the assertion following it

import Mathlib
import Definitions.Def_KieferWolfowitz_Convergence_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace KieferWolfowitz.Convergence

/-- Kiefer & Wolfowitz (1952), p. 465, the assertion after (3.19): if `n_1 < n_2 < ⋯` and
`E{K_{n_j} |z_{n_j} − θ|} → 0`, then `z_{n_j} − θ` converges stochastically to zero. Only Condition 3,
`c_n > 0`, `c_n → 0` and the integrability of `K_{n_j} |z_{n_j} − θ|` are used. -/
theorem subseq_tendstoInMeasure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (M : ℝ → ℝ) (θ : ℝ) (h3 : Cond3 M θ)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hc0 : Tendsto c atTop (𝓝 0))
    (z : ℕ → Ω → ℝ) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hint : ∀ j, Integrable (fun ω => K M c z (φ j) ω * |z (φ j) ω - θ|) P)
    (hlim : Tendsto (fun j => ∫ ω, K M c z (φ j) ω * |z (φ j) ω - θ| ∂P) atTop (𝓝 0)) :
    TendstoInMeasure P (fun j => z (φ j)) atTop (fun _ => θ) := by sorry

end KieferWolfowitz.Convergence
