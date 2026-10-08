-- Prove2me | Theorems.Thm_GittinsDAI_IndexTheorem_finite_horizon_stopping_sets
-- name    : GittinsDAI.IndexTheorem.finite_horizon_stopping_sets
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T10:45:10.153998+00:00
-- url     : https://prove2.me/theorems/81485025-b4dd-4ab7-b823-5d26547a1b67
-- title:
--   Section 4, Corollary 1 — the supremum in (5) is attained by $\Theta_0(t)=\{y:\nu^{M-t}(D,y)<\nu^M(D,x)\}$
-- statement:
--   Let $D$ be a bandit process as in the Section 4 Lemma: a Markov chain on a standard Borel state space $\Theta$ with transition kernel $P$, a measurable reward $R$ and discount factor $0<a<1$, with $E\{\sum_{t\ge 0} a^t|R(x(t))| \mid x(0)=x\}<\infty$ for every $x$. For a positive integer $M$ let
--   $$\nu^M(D,x) = \sup_{0<\tau\le M} \nu_\tau(D,x) \tag{5}$$
--   be the $M$-horizon index, the supremum of $\nu_\tau(D,x)=R_\tau(D,x)/W_\tau(D,x)$ over the stopping times $1\le\tau\le M$. Assume that every $\nu^m(D,\cdot)$, $m\in\mathbb N$, is a measurable function of the state.
--
--   **Corollary 1.** Fix a positive integer $M$ and a state $x$, and set
--   $$\Theta_0(t) = \{y\in\Theta : \nu^{M-t}(D,y) < \nu^M(D,x)\},\qquad t=1,2,\dots,M-1.$$
--   Let $\tau$ be the first $t\in\{1,\dots,M-1\}$ with $x(t)\in\Theta_0(t)$, and $\tau=M$ if there is none. Then $\tau$ is a stopping time with $1\le\tau\le M$, and it attains the supremum in (5):
--   $$\nu_\tau(D,x) = \nu^M(D,x).$$
--
--   Corollary 2 of the paper, that the right-hand side of (5) is unaltered if the stopping sets are restricted to the form $\{y : \nu^{M-t}(D,y)<\mu\}$ for some non-random $\mu$, follows by taking $\mu=\nu^M(D,x)$. The corollaries are the basis of the paper's numerical algorithm for the index (Section 7).
--
--   **Formalization Note** $\nu^M$ and the stopping rule are the definitions of `GittinsDAI.IndexTheorem.FiniteHorizon`. For $M=1$ the set of $t$ is empty and $\tau\equiv 1$. The standing integrability assumption and the standard Borel state space are as in the Lemma. The measurability of each $\nu^m(D,\cdot)$ is not stated by the paper for the finite-horizon indices; it is taken as a hypothesis, and it makes each $\Theta_0(t)$ measurable.
-- source:
--   Gittins, Bandit Processes and Dynamic Allocation Indices, J. R. Statist. Soc. B 41 (1979), p. 155, Section 4, Corollary 1 (with Eq. (5) and Corollary 2)

import Mathlib
import Definitions.Def_GittinsIndex
import Definitions.Def_AllocationIndices_Index
import Definitions.Def_GittinsDAI_IndexTheorem_FiniteHorizon
open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices

namespace GittinsDAI.IndexTheorem

/-- Gittins (1979), Section 4, Corollary 1, p. 155: for a positive integer `M`, the supremum in
(5), `ν^M(D, x) = sup_{0 < τ ≤ M} ν_τ(D, x)`, is attained by the stopping rule with the
time-dependent stopping sets `Θ₀(t) = {y : ν^{M−t}(D, y) < ν^M(D, x)}`, `t = 1, …, M − 1`
(stopping at `M` at the latest). The measurability of every `ν^m(D, ·)` is taken as the
hypothesis `hm`. -/
theorem finite_horizon_stopping_sets {S : Type*} [MeasurableSpace S] [StandardBorelSpace S]
    (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hint : DiscountedRewardIntegrable P r α)
    (hm : ∀ m : ℕ, Measurable (finiteHorizonIndex P r α m))
    (M : ℕ) (hM : 1 ≤ M) (x : S) :
    IsPositiveStoppingTime (corollaryStoppingTime P r α M x) ∧
      (∀ ω, corollaryStoppingTime P r α M x ω ≤ (M : ℕ∞)) ∧
      stoppedRatio P r α (corollaryStoppingTime P r α M x) x = finiteHorizonIndex P r α M x := by sorry

end GittinsDAI.IndexTheorem
