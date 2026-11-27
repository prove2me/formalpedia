-- Prove2me | Theorems.Thm_FragileBandit_CauchyTail_Supplement_theorem_3_counterexample
-- name    : FragileBandit.CauchyTail.Supplement.theorem_3_counterexample
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T00:04:47.775119+00:00
-- url     : https://prove2.me/theorems/b383c479-4ed1-459c-a196-545b5ad1e98c
-- title:
--   Theorem 3 (corrected: counterexample) — Assumptions 1–2 do not imply (23)
-- statement:
--   The full process generality of Theorem 3 admits a counterexample. For the Gaussian design family with unit variance, there exist two independent rested reward sequences and a measurable history policy that is $M_P$-pathwise convergent across all environments, with
--   $$\overline\Lambda_0(\theta)=\theta+\theta^2/2,\qquad\overline\Lambda_1(\theta)=\theta^2/2.$$
--   They satisfy Assumptions 1–2 and both standing reward-range conditions. Their long-run means are respectively $1$ and $0$, so the exponent prescribed for the second arm is
--   $$c_1=\inf_{z<0}\frac{(z-1)^2/2}{z^2/2}=1.$$
--   Nevertheless, for every $0<\gamma<1$ and all sufficiently large $T$,
--   $$\mathbb P_{\nu\pi}(N_1(T)>x)=0\quad\text{for every }x\in[(\log T)^{1+\gamma},(1-\gamma)T].$$
--   The theorem explicitly asserts failure of the corresponding lower power inequality. Thus it refutes (23) on the source's domain, rather than proving a restricted version.
--
--   This counterexample isolates information in early observations which the limiting CGF does not describe. Its full analytic construction and the global Definition 4 check are in DISPROOF.md: a bounded first reward encodes a finite random transient, and a prediction-checking allocation uses ordinary Gaussian KL-UCB as a permanent fallback on a mismatch. **Formalization Note** The existential counterexample remains an open Lean theorem, not a machine-checked proof. No tilt-consistency, iid, stationarity, mixing or change-of-measure premise is added. Definition 4 is instantiated at the Gaussian design, whose mean domain is $\mathbb R$; the policy property quantifies over every real reward table, using the published divergence without an extension.
--
--   Differences from the source:
--   - correction: Theorem 3 asserts the lower bound (23) for all pathwise convergent policies and independent rested processes satisfying Assumptions 1–2 → an existential counterexample with Gaussian limiting CGFs, distinct long-run means 1 and 0, exact exponent 1, eventually zero uniform tails, and explicit failure of (23); reason: independent eventually-constant sequences can encode their random finite transient in a bounded first reward; the scaled CGF remains mθ+θ²/2, while a policy verifies the prediction and falls back on any mismatch, satisfying Definition 4 globally (DISPROOF.md); no domain is excluded and no repair premise is assumed
--   - encoding: logarithmic lower bound (23), real-valued reward processes and one-based arm/pull indices → uniform power inequality, a law on canonical real reward tables, induced rested history measures, and Fin 2 with local indices starting at zero; reason: the exponent is the exact sum of rate-function ratios and equals 1 in the counterexample; zero probability keeps its −∞ logarithm, and a canonical table law preserves all serial dependence and inter-arm independence
-- source:
--   Fan and Glynn, The Fragility of Optimized Bandit Algorithms, arXiv:2109.13595v8, Theorem 3, printed p.21, PDF p.21, (23); Assumptions 1–2 and Definition 4, p.20; Appendix C, pp.44–45, (73)

import Mathlib
import Definitions.Def_FragileBandit_CauchyTail_Supplement_ProcessAsymptotics
import Definitions.Def_FragileBandit_CauchyTail_Supplement_PathwiseConvergence

set_option autoImplicit false

namespace FragileBandit.CauchyTail.Supplement

open MeasureTheory ProbabilityTheory Filter BanditAlgorithm
open scoped ENNReal Topology

/-- Counterexample to the full generality of Theorem 3, p.21, (23).
The smooth limiting CGFs do not control information about later rewards revealed early.
See DISPROOF.md for the independent finite-transient construction and the policy. -/
theorem theorem_3_counterexample :
    ∃ (ν : RestedEnvironment 2) (π : BanditPolicy 2),
      IndependentArms ν ∧
      AssumptionOne ν ∧ AssumptionTwo ν ∧
      FitsFamily (gaussianReal 0 1) ν ∧
      IsGaussianPathwiseConvergent π ∧
      (∀ (i : Fin 2) (θ : ℝ), limitingCGF ν i θ =
        (((if i = 0 then 1 else 0 : ℝ) * θ + θ ^ 2 / 2 : ℝ) : EReal)) ∧
      processMean ν 0 = 1 ∧ processMean ν 1 = 0 ∧
      processTailExponent (gaussianReal 0 1) ν 1 = 1 ∧
      (∀ γ : ℝ, 0 < γ → γ < 1 →
        ∀ᶠ T : ℕ in atTop, ∀ x ∈ tailWindow γ T, processTail ν π 1 T x = 0) ∧
      ¬ UniformTailLower (processTail ν π 1) (processTailExponent (gaussianReal 0 1) ν 1)
      := by sorry

end FragileBandit.CauchyTail.Supplement
