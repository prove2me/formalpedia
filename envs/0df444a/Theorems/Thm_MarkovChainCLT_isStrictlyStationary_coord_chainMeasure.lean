-- Prove2me | Theorems.Thm_MarkovChainCLT_isStrictlyStationary_coord_chainMeasure
-- name    : MarkovChainCLT.isStrictlyStationary_coord_chainMeasure
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T15:16:35.240912+00:00
-- url     : https://prove2.me/theorems/22ee3126-d66e-4f46-af33-db81823e2616
-- title:
--   A chain started from its invariant law is strictly stationary
-- statement:
--   Let $P$ be a Markov transition kernel on $\mathsf{X}$ and let $\pi$ be an invariant probability distribution for $P$, i.e. $\pi P = \pi$. Consider the law of the trajectory $(X_0, X_1, X_2, \dots)$ of the time-homogeneous Markov chain with kernel $P$ started from $X_0 \sim \pi$. Then the coordinate process $\{X_i\}_{i \ge 0}$ is **strictly stationary**: for every $k$, the shifted trajectory $(X_k, X_{k+1}, \dots)$ has the same law on the path space as $(X_0, X_1, \dots)$.
--
--   This is the classical fact that a Markov chain started in its stationary distribution is a stationary process. It follows from invariance by induction on the finite-dimensional distributions: $X_k \sim \pi$ for every $k$ because $\pi$ is invariant, and the conditional law of $(X_{k+1}, X_{k+2}, \dots)$ given $X_k$ is the same kernel-generated law for every $k$ by time-homogeneity; the two together determine the law of the shifted path.
--
--   Every mixing central limit theorem used in this mission (Theorems 3 and 5-8) assumes a *strictly stationary* sequence, so this lemma is the gateway that lets those theorems be applied to a Markov chain run from equilibrium.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Sections 3-4: the mixing coefficients and Theorems 3, 5-8 are stated for the stationary version of the chain (see also Meyn & Tweedie 1993, Ch. 17).

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem MarkovChainCLT.isStrictlyStationary_coord_chainMeasure {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant P π) :
    IsStrictlyStationary (chainMeasure P π) (fun i (ω : ℕ → X) => ω i) := by sorry
