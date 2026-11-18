-- Prove2me | Theorems.Thm_IAFTRL_theorem_3_2_i
-- name    : IAFTRL.theorem_3_2_i
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-18T04:21:08.700447+00:00
-- url     : https://prove2.me/theorems/f0bce1ed-c050-4c07-8aba-e815e34369d7
-- title:
--   Theorem 3.2(i) — information-acquisition lower bound on a sharp curve: $c^*_{\rm ctr}=8/\tau$ and $\liminf \mathrm{Reg}_T/\log T\ge 7/(16\tau)$
-- statement:
--   **Setting.** Let
--   $$
--   \mathcal A_{\rm curve}=\Big\{a(s)=\Big(-\frac12+\frac s4,\ \frac{s+s^2}{4}\Big):0\le s\le1\Big\},\qquad \theta_\tau=(\tau,0),\quad 0<\tau\le1 .
--   $$
--   The unique optimal action of $\theta_\tau$ is $a(0)=(-\tfrac12,0)$, with gap $\Delta(a(s))=\tau s/4$. The feedback is a sign observation of the linear mean: playing $a$ yields $Y\in\{\pm1\}$ with $\mathbb E[Y]=a^\top\theta$ (Proposition H.1). A policy is *consistent* if it plays only actions of $\mathcal A_{\rm curve}$ and satisfies $\mathrm{Reg}_{T,\theta}=o(T^\alpha)$ for every $\alpha>0$ and every sharp stochastic instance $\theta$ on this curve, i.e. every $\theta$ with $\|\theta\|_{\mathcal A}\le1$, a unique optimal action, and geometric sharpness.
--
--   **Claim.** The centered information-acquisition complexity (1.4) of $(\mathcal A_{\rm curve},\theta_\tau)$ is
--   $$
--   c^*_{\rm ctr}(\mathcal A_{\rm curve},\theta_\tau)=\frac8\tau ,
--   $$
--   and every consistent policy satisfies
--   $$
--   \liminf_{T\to\infty}\frac{\mathrm{Reg}_{T,\theta_\tau}}{\log T}\ \ge\ \frac{7}{16\tau}=\frac{7}{128}\,c^*_{\rm ctr}(\mathcal A_{\rm curve},\theta_\tau).
--   $$
--
--   On this sharp curve the minimum positive gap is zero. The claim shows that the logarithmic term $c^*_{\rm ctr}\log T$ in the upper bound of Theorem 3.1 cannot be improved beyond a constant factor.
--
--   **Formalization Note** $c^*_{\rm ctr}$ is `cstarCtr curve θ ![-1/2, 0]`. The environment is `signEnv θ`, and consistency is `IsConsistentOn curve (sharpInstances curve) π` with `IsSupportedLinearPolicy curve π`. The lower limit is stated in its elementary form: for every $\varepsilon>0$, eventually $(7/(16\tau)-\varepsilon)\log T\le\mathrm{Reg}_{T,\theta_\tau}$.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Section 3.3, Theorem 3.2 (first bullet), p.25; proof in Appendix H.1, Proposition H.1 (H.3), pp.191–194

import Mathlib
import Definitions.Def_LinearBanditProtocol
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL
import Definitions.Def_IAFTRL_SignModel

namespace IAFTRL

open MeasureTheory ProbabilityTheory Matrix BanditAlgorithm Filter Topology

/-- **Theorem 3.2, first part (information-acquisition lower bound).** Zhao–Tan,
*Best-of-Both-Worlds FTRL for Linear Bandits* (STOC submission version), Theorem 3.2, p.25:
"On `A_curve = {(−1/2 + s/4, (s + s²)/4) : 0 ≤ s ≤ 1}`, `θ_τ = (τ, 0)` and `0 < τ ≤ 1`, we have
`c*_ctr = 8/τ`. Every consistent policy satisfies
`liminf_{T→∞} Reg_{T,θ_τ} / log T ≥ 7/(16τ) = (7/128) c*_ctr`."
The feedback model is that of Proposition H.1 (p.193): sign observations of the linear mean, and
consistency is on the sharp stochastic instances on this curve.

The optimal action of `θ_τ` is `a(0) = (−1/2, 0)`, which is the `a*` of `c*_ctr` in (1.4). The
lower limit is stated in its elementary form: for every `ε > 0`, eventually
`(7/(16τ) − ε) log T ≤ Reg_{T,θ_τ}`. -/
theorem theorem_3_2_i (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    let curve : Set (Fin 2 → ℝ) := {a | ∃ s ∈ Set.Icc (0 : ℝ) 1, a = ![-1 / 2 + s / 4, (s + s ^ 2) / 4]}
    let θ : Fin 2 → ℝ := ![τ, 0]
    cstarCtr curve θ ![-1 / 2, 0] = 8 / τ ∧
    ∀ π : LinearBanditPolicy 2, IsSupportedLinearPolicy curve π →
      IsConsistentOn curve (sharpInstances curve) π →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop,
        (7 / (16 * τ) - ε) * Real.log T ≤ (signEnv θ).regret curve π T := by sorry

end IAFTRL
