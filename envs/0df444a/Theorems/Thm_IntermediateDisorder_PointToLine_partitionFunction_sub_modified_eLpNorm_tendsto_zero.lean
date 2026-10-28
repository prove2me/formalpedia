-- Prove2me | Theorems.Thm_IntermediateDisorder_PointToLine_partitionFunction_sub_modified_eLpNorm_tendsto_zero
-- name    : IntermediateDisorder.PointToLine.partitionFunction_sub_modified_eLpNorm_tendsto_zero
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-24T17:06:20.665416+00:00
-- url     : https://prove2.me/theorems/db5b5e97-fd88-44a1-9857-1eb83919daf4
-- title:
--   $e^{-n\lambda(\beta n^{-1/4})}Z_n^\omega(\beta n^{-1/4})-\mathfrak z_n^\omega(\beta n^{-1/4})\to0$ in $L^2(Q)$
-- statement:
--   Let the environment variables $\omega(i,x)$, $i\ge1$, $x\in\mathbb Z$, be i.i.d. with mean zero and variance one, and suppose there is $\beta_0>0$ such that $\lambda(b)=\log Q\big(e^{b\,\omega}\big)<\infty$ for all $0<b<\beta_0$. Let $\beta>0$ and $\beta_n=\beta n^{-1/4}$. Then the normalised point-to-line partition function and the modified partition function (4) are asymptotically equal in $L^2(Q)$:
--
--   $$\big\|\,e^{-n\lambda(\beta_n)}Z_n^\omega(\beta_n)-\mathfrak z_n^\omega(\beta_n)\,\big\|_{L^2(Q)}\;\longrightarrow\;0\qquad(n\to\infty).$$
--
--   Here $Z_n^\omega(\beta)=\mathbf P\big[e^{\beta\sum_{i=1}^n\omega(i,S_i)}\big]$ and $\mathfrak z_n^\omega(\beta)=\mathbf P\big[\prod_{i=1}^n(1+\beta\,\omega(i,S_i))\big]$, averages over the $2^n$ paths of the simple random walk started at $0$.
--
--   Role: this is the comparison step in the proof of Proposition 5.4. Combined with Proposition 5.3 ($\mathfrak z_n^\omega(\beta n^{-1/4})\to\mathcal Z_{\sqrt2\beta}$ in law), convergence in $L^2$, hence in probability, of the difference transfers the limit law from $\mathfrak z_n$ to $e^{-n\lambda(\beta n^{-1/4})}Z_n^\omega(\beta n^{-1/4})$ (Slutsky), which is Theorem 2.1.
--
--   **Formalization Note**: $\lambda$ is Mathlib's cumulant generating function `cgf (ω (1, 0)) Q` and "$\lambda(b)<\infty$" is integrability of $e^{b\,\omega(1,0)}$; the environment assumptions are the published `IsStdEnvironment`; the $L^2$ norm is Mathlib's `eLpNorm _ 2 Q`. For the finitely many $n$ with $\beta n^{-1/4}\ge\beta_0$ the integrand may involve default values; the limit statement ignores finitely many terms.
-- source:
--   Alberts, Khanin, Quastel, The intermediate disorder regime for directed polymers in dimension 1+1, arXiv:1202.4398v3, https://arxiv.org/abs/1202.4398, proof of Proposition 5.4, p. 31 (L^2 comparison of e^{-n lambda} Z_n with the modified partition function (4))

import Mathlib
import Definitions.Def_IntermediateDisorder_PointToLine_Environment

namespace IntermediateDisorder.PointToLine

open MeasureTheory ProbabilityTheory Filter Topology

theorem partitionFunction_sub_modified_eLpNorm_tendsto_zero {Ω : Type*} [MeasurableSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q] {ω : ℕ × ℤ → Ω → ℝ}
    (hω : IsStdEnvironment ω Q)
    (hexp : ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ b : ℝ, 0 < b → b < β₀ →
      Integrable (fun a => Real.exp (b * ω (1, 0) a)) Q) (β : ℝ) (hβ : 0 < β) :
    Tendsto (fun n : ℕ => eLpNorm (fun a =>
        Real.exp (-(n : ℝ) * cgf (ω (1, 0)) Q (β * (n : ℝ) ^ (-(1 / 4 : ℝ)))) *
            partitionFunction ω n (β * (n : ℝ) ^ (-(1 / 4 : ℝ))) a -
          modifiedPartitionFunction ω n (β * (n : ℝ) ^ (-(1 / 4 : ℝ))) a) 2 Q)
      atTop (𝓝 0) := by sorry

end IntermediateDisorder.PointToLine
