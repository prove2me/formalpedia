-- Prove2me | Theorems.Thm_GittinsDAI_IndexTheorem_optimal_stopping_set
-- name    : GittinsDAI.IndexTheorem.optimal_stopping_set
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T10:26:34.412992+00:00
-- url     : https://prove2.me/theorems/296dc16b-b9de-49df-8f91-f8f35f8354f3
-- title:
--   Section 4, Lemma — the supremum in (2) is attained by the stopping set $\Theta_0=\{y:\nu(D,y)<\nu(D,x)\}$
-- statement:
--   Let $D$ be a bandit process: a Markov chain $x(0),x(1),\dots$ on a standard Borel state space $\Theta$ with transition kernel $P$, a measurable reward function $R$, and discount factor $0<a<1$, such that for every initial state $x$
--   $$E\Big\{\sum_{t=0}^{\infty} a^t |R(x(t))| \,\Big|\, x(0)=x\Big\} < \infty .$$
--   The dynamic allocation index (DAI) of $D$ in state $x$ is (Eq. (2), p. 154)
--   $$\nu(D,x) = \sup_{\tau>0} \nu_\tau(D,x) = \sup_{\tau>0} \frac{E\{\sum_{t=0}^{\tau-1} a^t R(x(t)) \mid x(0)=x\}}{E\{\sum_{t=0}^{\tau-1} a^t \mid x(0)=x\}},$$
--   the supremum over stopping times $\tau\ge 1$ (possibly infinite) of the chain. Assume that $\nu(D,\cdot)$ is a measurable function of the state, as the paper asserts on p. 151.
--
--   **Lemma.** Fix a state $x$ and let
--   $$\Theta_0 = \{y\in\Theta : \nu(D,y) < \nu(D,x)\}.$$
--   Let $\tau$ be the first process time $t\ge 1$ with $x(t)\in\Theta_0$ ($\tau=\infty$ if there is none). Then $\tau$ is a stopping time with $\tau\ge 1$, and the supremum in (2) is attained by it:
--   $$\nu_\tau(D,x) = \nu(D,x).$$
--
--   The Lemma identifies an optimal stopping rule for the index: continue while the index stays at least its initial value. It is the basis of the paper's characterization of the index and of its Corollary 1.
--
--   **Formalization Note** Time is indexed from $0$, and stopping times take values in $\mathbb{N}\cup\{\infty\}$; the stopping set is applied "from process time 1 onwards" (p. 154), which is what `hittingTime` does. The paper's standing assumption that "the supremum of the total expected reward is finite" (p. 151) is read as the integrability hypothesis above (Lattimore–Szepesvári Assumption 35.6), which is slightly stronger. The paper's state space is a measurable space whose singletons are measurable; the Lean asks for a standard Borel space, as the published sufficiency theorem does. The measurability of $\nu(D,\cdot)$, which the paper asserts (p. 151 and point (iii) of the proof, p. 155), is taken as a hypothesis; it makes $\Theta_0$ measurable.
-- source:
--   Gittins, Bandit Processes and Dynamic Allocation Indices, J. R. Statist. Soc. B 41 (1979), p. 154, Section 4, Lemma (with Eq. (2))

import Mathlib
import Definitions.Def_GittinsIndex
import Definitions.Def_AllocationIndices_Index
open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices

namespace GittinsDAI.IndexTheorem

/-- Gittins (1979), Section 4, Lemma, p. 154: the supremum in (2) is attained by the stopping
rule with stopping set `Θ₀ = {y : ν(D, y) < ν(D, ξ)}` (applied from process time `1` onwards).
The measurability of `ν(D, ·)` is asserted by the paper on p. 151 and is taken as the hypothesis
`hg`. -/
theorem optimal_stopping_set {S : Type*} [MeasurableSpace S] [StandardBorelSpace S]
    (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hint : DiscountedRewardIntegrable P r α)
    (hg : Measurable (gittinsIndex P r α)) (ξ : S) :
    IsPositiveStoppingTime (hittingTime {y | gittinsIndex P r α y < gittinsIndex P r α ξ}) ∧
      stoppedRatio P r α (hittingTime {y | gittinsIndex P r α y < gittinsIndex P r α ξ}) ξ =
        gittinsIndex P r α ξ := by sorry

end GittinsDAI.IndexTheorem
