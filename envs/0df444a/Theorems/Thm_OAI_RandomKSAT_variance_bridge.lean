-- Prove2me | Theorems.Thm_OAI_RandomKSAT_variance_bridge
-- name    : OAI.RandomKSAT.variance_bridge
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T18:20:12.822435+00:00
-- url     : https://prove2.me/theorems/b9515eea-4878-41cd-845b-1186482b0fa8
-- title:
--   Variance comparison $\operatorname{Var} f\le 2\operatorname{Var} g+2\,\mathbb E[(f-g)^2]$
-- statement:
--   Let $(\Omega,\mathcal F,\mu)$ be a probability space and let $f,g:\Omega\to\mathbb R$ be square-integrable random variables, that is $f,g\in L^2(\mu)$. Write $\operatorname{Var}_\mu(h)=\int_\Omega\big(h-\int_\Omega h\,d\mu\big)^2\,d\mu$ for the variance of $h\in L^2(\mu)$.
--
--   **Theorem.** Under these assumptions,
--   $$
--   \operatorname{Var}_\mu(f)\le 2\operatorname{Var}_\mu(g)+2\int_\Omega (f-g)^2\,d\mu .
--   $$
--
--   The inequality transfers variance bounds between two random variables that are close in $L^2$: if $\int(f-g)^2\,d\mu$ is bounded, the variances of $f$ and $g$ agree up to a factor $2$ and an additive constant. In the variance analysis of random $k$-SAT clause streams it is applied in both directions to the uncapped first failure time and the failure time capped at $\lfloor Bn\rfloor$, whose mean-square difference is bounded uniformly in $n$ when $B\ge U(k)$.
--
--   **Formalization Note** Square integrability is the hypothesis `MemLp f 2 μ` (almost-everywhere strong measurability and a finite second moment), and the probability measure is given by the instance `IsProbabilityMeasure μ`. Mathlib's `variance` is the real-valued version of the extended variance `evariance`; for square-integrable functions it is the usual variance.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/CapBridge.lean#L134-L153

import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiniteVariance
import Definitions.Def_OAI_Probability_SATVariance_LifetimePotential
import Definitions.Def_OAI_Probability_SATVariance_RootDisintegration__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiberRefresh
import Definitions.Def_OAI_Probability_SATVariance_PairEvolution
import Definitions.Def_OAI_Probability_SATVariance_HiddenTests
import Definitions.Def_OAI_Probability_SATVariance_WeightedRewards
import Definitions.Def_OAI_Probability_SATVariance_CountMoments
import Definitions.Def_OAI_Probability_SATVariance_SupportProbabilities__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_OmissionCompression
import Definitions.Def_OAI_Probability_SATVariance_CapBridge

open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem OAI.RandomKSAT.variance_bridge.{u_1} {Ω : Type u_1} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    variance f μ ≤ 2*variance g μ + 2*(∫ ω, (f ω-g ω)^2 ∂μ) := by sorry
