-- Prove2me | Theorems.Thm_IntermediateDisorder_PointToLine_partitionFunction_tendstoInDistribution_chaos
-- name    : IntermediateDisorder.PointToLine.partitionFunction_tendstoInDistribution_chaos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:24:53.250286+00:00
-- url     : https://prove2.me/theorems/65ecb5d3-897d-47ef-b7cb-d4eb6287418e
-- title:
--   Theorem 2.1 / Proposition 5.4 — $e^{-n\lambda(\beta n^{-1/4})}Z_n^\omega(\beta n^{-1/4})\to\mathcal Z_{\sqrt2\beta}$ in law
-- statement:
--   Let the environment variables $\omega(i,x)$, $i\ge1$, $x\in\mathbb Z$, be i.i.d. with mean zero and variance one, and suppose there is $\beta_0>0$ such that
--
--   $$\lambda(b):=\log Q\big(e^{b\,\omega}\big)<\infty\qquad\text{for all }0<b<\beta_0 .$$
--
--   Let $\beta>0$, let $W$ be a white noise on $[0,1]\times\mathbb R$ with multiple stochastic integrals $I=(I_k)$, and let $\mathcal Z_{\sqrt2\beta}$ be the Wiener chaos (7). Then the rescaled point-to-line partition function of the directed polymer converges in law:
--
--   $$e^{-n\lambda(\beta n^{-1/4})}\,Z_n^\omega(\beta n^{-1/4})\xrightarrow{(d)}\mathcal Z_{\sqrt2\beta}=1+\sum_{k=1}^\infty(\sqrt2\beta)^k\int_{\Delta_k}\int_{\mathbb R^k}\prod_{i=1}^kW(t_i,x_i)\,\varrho(t_i-t_{i-1},x_i-x_{i-1})\,dx_i\,dt_i\qquad(n\to\infty).$$
--
--   Here $Z_n^\omega(\beta)=\mathbf P[e^{\beta H_n^\omega(S)}]$ is the average of $e^{\beta\sum_{i=1}^n\omega(i,S_i)}$ over the $2^n$ paths of the simple random walk started at $0$, $\Delta_k=\{0=t_0<t_1<\dots<t_k\le1\}$, $x_0=0$, and $\varrho(t,x)=e^{-x^2/2t}/\sqrt{2\pi t}$.
--
--   This is the main theorem of the paper: in the intermediate disorder regime $\beta_n=\beta n^{-1/4}$ the normalised partition function neither tends to a constant (weak disorder) nor to zero (strong disorder) but to a universal random limit, the Wiener chaos solution of the stochastic heat equation with multiplicative noise evaluated at time $1$ and integrated in space. As a corollary $\log Z_n^\omega(\beta n^{-1/4})-n\lambda(\beta n^{-1/4})$ converges in law.
--
--   **Formalization Note** $\lambda$ is Mathlib's cumulant generating function of $\omega(1,0)$, and "$\lambda(b)<\infty$" is integrability of $e^{b\,\omega(1,0)}$. For the finitely many $n$ with $\beta n^{-1/4}\ge\beta_0$, $\lambda(\beta n^{-1/4})$ may take a default value; convergence in law ignores finitely many terms. The mean-zero/variance-one normalisation is the standing assumption of Section 5, under which Proposition 5.4 is proved; Theorem 2.1's "with or without the normalizations" is not formalized (with variance $\sigma^2$ the limit would be $\mathcal Z_{\sqrt2\beta\sigma}$). The limit is the chaos of an arbitrary white noise with its multiple integrals, on any probability space; Section 3.2's existence theorem shows such a pair exists.
-- source:
--   Alberts, Khanin, Quastel, The intermediate disorder regime for directed polymers in dimension 1+1, arXiv:1202.4398v3, p. 7, Theorem 2.1 (second bullet; (7) on p. 8); proved as Proposition 5.4, p. 31

import Mathlib
import Definitions.Def_IntermediateDisorder_PointToLine_Environment
import Definitions.Def_IntermediateDisorder_PointToLine_WienerChaos

namespace IntermediateDisorder.PointToLine

open MeasureTheory ProbabilityTheory Filter

/-- Theorem 2.1 (second bullet), proved as Proposition 5.4: for an i.i.d. environment with mean
zero and variance one such that `λ(b) = log Q e^{bω} < ∞` for all `0 < b < β₀` (some
`β₀ > 0`), and `β > 0`, `e^{-nλ(βn^{-1/4})} Z_n^ω(βn^{-1/4}) → 𝒵_{√2β}` in distribution,
where `𝒵_{√2β}` is the Wiener chaos (7) of any white noise on `[0,1] × ℝ`. -/
theorem partitionFunction_tendstoInDistribution_chaos {Ω : Type*} [MeasurableSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q] {ω : ℕ × ℤ → Ω → ℝ}
    (hω : IsStdEnvironment ω Q)
    (hexp : ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ b : ℝ, 0 < b → b < β₀ →
      Integrable (fun a => Real.exp (b * ω (1, 0) a)) Q)
    {Ω' : Type*} [MeasurableSpace Ω'] {Q' : Measure Ω'} [IsProbabilityMeasure Q']
    (W : Set (ℝ × ℝ) → Ω' → ℝ) (I : (k : ℕ) → Lp ℝ 2 (kernelMeasure k) →L[ℝ] Lp ℝ 2 Q')
    (hW : IsWhiteNoise W Q') (hI : IsMultipleIntegral W Q' I) (β : ℝ) (hβ : 0 < β) :
    TendstoInDistribution
      (fun (n : ℕ) a => Real.exp (-(n : ℝ) * cgf (ω (1, 0)) Q (β * (n : ℝ) ^ (-(1 / 4 : ℝ)))) *
        partitionFunction ω n (β * (n : ℝ) ^ (-(1 / 4 : ℝ))) a)
      atTop (wienerChaos I (Real.sqrt 2 * β)) (fun _ => Q) Q' := by sorry

end IntermediateDisorder.PointToLine
