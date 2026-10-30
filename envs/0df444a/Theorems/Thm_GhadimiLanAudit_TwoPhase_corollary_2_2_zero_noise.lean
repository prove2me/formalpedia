-- Prove2me | Theorems.Thm_GhadimiLanAudit_TwoPhase_corollary_2_2_zero_noise
-- name    : GhadimiLanAudit.TwoPhase.corollary_2_2_zero_noise
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:51:14.45815+00:00
-- url     : https://prove2.me/theorems/3d8d3bac-17fc-4620-b4a5-081f3313bb5a
-- title:
--   Corollary 2.2 (2.14), zero-noise companion (corrected: step completed by 1/L)
-- statement:
--   Consider the smooth lower-bounded objective and actual gradient described above, with exact noise level $\sigma=0$. Run $N\ge1$ full RSG iterations with the completed step $\gamma=1/L$, under finite A1, and choose $R$ independently of the noise with mass function (2.3), here uniform on $1,\ldots,N$. With $f^*=\inf f$ and $D_f=\sqrt{2(f(x_1)-f^*)/L}$, the squared gradient at the stored point $x_R$ is integrable and
--
--   $$\frac1L\mathbb E\|g(x_R)\|^2\le\frac{LD_f^2}{N}.$$
--
--   This supplies the missing zero-noise branch of the nonconvex bound (2.14). Its positive-noise companion is the existing Open item `GhadimiLan.TwoPhase.corollary_2_2`, included by reference. The independent convex bound (2.15) is outside this mission.
--
--   **Formalization Note** The gradient and initial gap use the shared full-domain problem; the infimum need not be attained. The output is recovered from the full run's stored query, so no extra oracle evaluation is hidden in its definition.
--
--   Differences from the source:
--   - correction: Eq. (2.13) divides by sigma, with sigma allowed to be zero by A1 → the zero-noise companion uses gamma=1/L and bound L D_f^2/N; the positive-noise companion is the published reference GhadimiLan.TwoPhase.corollary_2_2; reason: on the singleton exact quadratic oracle f(x)=x^2/2, x1=1, L=Dt=1, sigma=0, all A1 assumptions hold but the printed step divides by zero; this supplies precisely the missing branch of (2.14)
--   - reading: A1(a) writes an expectation of an oracle at a random input → the conditional mean given past query information equals the actual gradient; reason: Eq. (2.10), p. 7 uses this conditional interpretation; the error second moment remains unconditional
--   - generalization: Borel noise and probability spaces with A1 along the source sequence → arbitrary measurable noise and probability spaces, with A1 required only through the executed finite horizon; reason: the Borel source model and its all-time A1 specialize to these laws; no source instance is lost
--   - encoding: one-based random-index RSG trajectory and implicit integrability → computed Euclidean trajectory and stored query lookup, with genuine integrability of every oracle return and squared error; reason: the finite-query interface expresses the same expectations and index distribution without using integral defaults
-- source:
--   Ghadimi and Lan, Stochastic First- and Zeroth-Order Methods for Nonconvex Stochastic Programming, arXiv:1309.5549v1, https://arxiv.org/abs/1309.5549v1, p. 8, Corollary 2.2, nonconvex (2.13)–(2.14), zero-noise completion; p. 6, Theorem 2.1(a), (2.4)–(2.5)

import Definitions.Def_GhadimiLanAudit_TwoPhase_Sampling

open MeasureTheory ProbabilityTheory

namespace GhadimiLanAudit.TwoPhase

/-- Corollary 2.2, nonconvex (2.14), p. 8: the missing zero-noise branch.
Correction to undefined (2.13): γ=1/L when σ=0. For f(x)=x²/2, x1=1,
L=Dt=1 and exact oracle, all A1 hypotheses hold but (2.13) divides by zero.
The positive-noise clause is the separate published reference, not re-posed here. -/
theorem corollary_2_2_zero_noise {n N : ℕ} {Ξ Ω : Type*}
    [MeasurableSpace Ξ] [MeasurableSpace Ω]
    (P : Problem n Ξ) (hσ : P.σ = 0)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hN : 1 ≤ N)
    (ξ : ℕ → Ω → Ξ) (R : Ω → ℕ) (hlaw : RunLaw P μ N ξ R) :
    Integrable (fun ω => ‖P.g ((candidateExec P N ξ R ω).value.1)‖ ^ 2) μ ∧
    (1 / P.L) * ∫ ω, ‖P.g ((candidateExec P N ξ R ω).value.1)‖ ^ 2 ∂μ ≤
      P.L * distanceScale P ^ 2 / (N : ℝ) := by sorry

end GhadimiLanAudit.TwoPhase
