-- Prove2me | Theorems.Thm_LogSobolevMC_Metropolis_corollary_3_8
-- name    : LogSobolevMC.Metropolis.corollary_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:59:08.206539+00:00
-- url     : https://prove2.me/theorems/a152f7c8-2b8b-4ebd-ac3d-cbf2be3471df
-- title:
--   Corollary 3.8, p. 724 — ‖k_xⁿ − 1‖₂ ≤ (1 + 2e²)^{1/2}e^{−c} for n ≥ (4α)⁻¹ log log(1/π(x)) + c/λ_* + 1
-- statement:
--   Let $K$ be an irreducible Markov kernel on a finite set $\mathcal X$ with invariant probability $\pi$ charging every point, and assume $(K,\pi)$ is reversible. Let $\alpha$ be its log-Sobolev constant, $\lambda$ its spectral gap, $\beta_{\min}$ its smallest eigenvalue, and set $\lambda_*=\min\{\lambda,1+\beta_{\min}\}$, assumed positive. Let $x\in\mathcal X$ with $\pi(x)\le 1/e$, and write $k^m_x(y)=K^m(x,y)/\pi(y)$ for the density of $K^m(x,\cdot)$ with respect to $\pi$. Then for every $c>0$,
--
--   $$\|k^m_x-1\|_2\le(1+2e^2)^{1/2}e^{-c}\qquad\text{for } m\ge\frac1{4\alpha}\log\log\frac1{\pi(x)}+\frac{c}{\lambda_*}+1.$$
--
--   This is the discrete-time form of the chi-square bound of Theorem 3.7: the log-Sobolev constant enters only through a doubly logarithmic term, and $1+\beta_{\min}$ accounts for near-periodicity.
--
--   **Formalization Note** $m$ is a natural number and the threshold is compared in $\mathbb R$. The hypothesis $\lambda_*>0$, stated as $1+\beta_{\min}>0$, is added: when $\beta_{\min}=-1$ the page's $c/\lambda_*$ is $+\infty$ and the claim is empty, while Lean's $c/0=0$ would make it false. The paper's second statement (the bound on $\sup_{x,y}|k^{2n}(x,y)-1|$) is not included.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), p. 724, Corollary 3.8 (first statement)

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_LogSobolevMC_Metropolis_Setting

namespace LogSobolevMC.Metropolis

/-- Corollary 3.8, p. 724 (first statement): for a reversible irreducible chain `(K, π)` and
a state `x` with `π(x) ≤ 1/e`, set `λ_* = min{λ, 1 + β_min}` (assumed positive). Then the
discrete-time density `k_xᵐ(y) = Kᵐ(x, y)/π(y)` satisfies
`‖k_xᵐ − 1‖₂ ≤ (1 + 2e²)^{1/2} e^{−c}` for `m ≥ (1/(4α)) log log (1/π(x)) + c/λ_* + 1`, `c > 0`. -/
theorem corollary_3_8 {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π) (hπpos : ∀ x, 0 < π x)
    (hirr : MarkovMixing.Irreducible K) (hrev : MarkovMixing.DetailedBalance K π)
    (hβ : 0 < 1 + betaMin K π)
    (x : V) (hx : π x ≤ Real.exp (-1)) (c : ℝ) (hc : 0 < c) (m : ℕ)
    (hm : (4 * LogSobolevMC.ChiSquare.logSobolev K π)⁻¹ * Real.log (Real.log (1 / π x)) +
        c / min (LogSobolevMC.ChiSquare.gap K π) (1 + betaMin K π) + 1 ≤ (m : ℝ)) :
    LogSobolevMC.ChiSquare.lpNorm π 2 (fun y => (K ^ m) x y / π y - 1) ≤
      Real.sqrt (1 + 2 * Real.exp 2) * Real.exp (-c) := by sorry

end LogSobolevMC.Metropolis
