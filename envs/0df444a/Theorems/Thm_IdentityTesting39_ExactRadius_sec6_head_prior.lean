-- Prove2me | Theorems.Thm_IdentityTesting39_ExactRadius_sec6_head_prior
-- name    : IdentityTesting39.ExactRadius.sec6_head_prior
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:54:47.758922+00:00
-- url     : https://prove2.me/theorems/65d00b01-b30a-4e38-9519-4e1ef97bcc95
-- title:
--   §6 — a normalized prior entirely on strict alternatives
-- statement:
--   There is an absolute $j_0>0$. Let $q$ have a largest atom $h\in[1/8,1)$, set $\alpha=1-h$, and let $\varepsilon$ be any nonempty strict radius. For real $n>0$ with $n\alpha\ge1$,
--
--   $$J_n^+(q,\varepsilon)\le j_0\quad\Longrightarrow\quad\exists\pi:\quad \pi\{p:\operatorname{TV}(p,q)>\varepsilon\}=1,\qquad \operatorname{TV}\!\left(\mathbb E_{p\sim\pi}\bigotimes_i\operatorname{Poi}(np_i),\bigotimes_i\operatorname{Poi}(nq_i)\right)\le\tfrac14.$$
--
--   The prior is a probability measure almost surely on probability vectors, entirely in the strict alternative. Its observation law is the full mixture. This is stronger than the constant far-mass conclusion needed in the separate constant-radius construction.
--
--   Differences from the source:
--   - encoding: a finite domain with k labels → an arbitrary finite label type ι, with k its cardinality; reason: finite relabeling changes no instance and permits the reservoir quotient
--   - encoding: minima over scalar tuples on the relevant coordinates → law-defined moments, real infima with explicit attainment where asserted, and zero unused head slots; reason: zeroing unused slots is a coordinate convention; infeasible deficit values are never used
--   - encoding: universal O or Ω comparison constants → positive existential constants precede all instance data and label types; reason: this is the universal meaning of the source asymptotics
--   - encoding: normalized prior supported on strict alternatives → a probability measure almost surely a probability vector and almost surely strictly ε-far; reason: measure-theoretic support here means concentration on the source event, not topological support
-- source:
--   Zhijie Zheng, An Exact-Radius Convex Characterization of Discrete Identity Testing, STOC 2027 submission #39 (October 2026), p.7, §6, construction in §§6.1–6.3, pp.7–9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/39.pdf

import Definitions.Def_IdentityTesting39_ExactRadius_PoissonExperiments

open MeasureTheory
open scoped ENNReal

namespace IdentityTesting39.ExactRadius

/-- §6, printed pp.7–9 / PDF pp.8–10, universal constants at h_*=1/8. -/
theorem sec6_head_prior :
    ∃ j₀ : ℝ, 0 < j₀ ∧
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (q : ι → ℝ) (ε n : ℝ) (i₀ : ι),
      ProbabilityVector q → StrictRadius q ε → Largest q i₀ →
      1/8 ≤ q i₀ → q i₀ < 1 → 0 < n → 1 ≤ n*(1-q i₀) →
      programValue q ε n (.excess i₀) ≤ j₀ →
      ∃ π : Measure (ι → ℝ), NormalizedPrior π ∧
        (∀ᵐ p ∂π, ε < FoundationsRL.GeneralDM.totalVariationDiscrete p q) ∧
        MarkovChainCLT.tvDist (poissonMixture n π) (poissonExperiment n q) ≤ 1/4 := by sorry

end IdentityTesting39.ExactRadius
