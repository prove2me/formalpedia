-- Prove2me | Theorems.Thm_KendallQueues_GIMs_theorem4_conditional_laws
-- name    : KendallQueues.GIMs.theorem4_conditional_laws
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:46:00.576978+00:00
-- url     : https://prove2.me/theorems/db6d1b89-0692-40d4-90a9-415b0e1ecf96
-- title:
--   Theorem IV, p. 350 — in GI/M/s a positive queue is geometric and a positive wait is exponential
-- statement:
--   Consider the queueing system GI/M/s: $s\ge1$ servers, independent inter-arrival times of law $A$ on $[0,\infty)$ with mean $a\in(0,\infty)$, and independent negative-exponential service times of mean $b>0$, first come first served. Let $P$ be the transition matrix (8)–(14) of the chain imbedded at arrival epochs, whose state $i$ is the number of persons an arriving customer finds ahead. Suppose
--   $$\rho=\frac{b}{sa}<1,$$
--   and let $\lambda$ be a root of $F(\lambda)=\lambda$ in $0<\lambda<1$, where $F(\lambda)=\int_0^\infty e^{-(1-\lambda)su/b}\,dA(u)$.
--
--   Then the chain has a limiting distribution $\pi$ ($p^n_{ij}\to\pi_j$ for all $i,j$, $\sum_j\pi_j=1$), and in this equilibrium, with $Q=\max(i-s,0)$ the queue size and $w$ the waiting time met by an arriving customer:
--
--   1. $\Pr(Q>0)>0$, and when $Q$ is known to be positive its conditional distribution is
--   $$\Pr(Q=n\mid Q>0)=(1-\lambda)\lambda^{n-1}\qquad(n=1,2,3,\dots);$$
--   2. $\Pr(w>0)>0$, and when $w$ is known to be positive its conditional distribution is negative-exponential with mean
--   $$c=\frac{b}{s(1-\lambda)},$$
--   that is, $\Pr(w>t\mid w>0)=e^{-t/c}$ for $t\ge0$ (density $e^{-w/c}/c$ on $0<w<\infty$).
--
--   The waiting-time half generalizes W. L. Smith's observation for a single server: whatever the input distribution and the number of servers, exponential service produces an exponential waiting time apart from an atom at the origin.
--
--   **Formalization Note** The conditional laws are stated multiplied out: $\Pr(Q=n)=\Pr(Q>0)(1-\lambda)\lambda^{n-1}$ for $n\ge1$, and $\Pr(w>t)=\Pr(w>0)e^{-t/c}$ for $t\ge0$, together with the positivity of $\Pr(Q>0)=1-\Pr(Q=0)$ and $\Pr(w>0)=1-\Pr(w\le0)$. The law of $w$ is the Erlang mixture of p. 349 (`waitCDF`). The limiting distribution $\pi$ is asserted to exist, not supplied. $\lambda$ is any root of $F(\lambda)=\lambda$ in $(0,1)$; the referenced uniqueness theorem makes it the root.
-- source:
--   Kendall (Ann. Math. Statist. 24, 1953), §7, p. 349 (preamble to II–IV, eq. (18), law of w) and p. 350, Theorem IV, eqs. (23)–(25)

import Mathlib
import Definitions.Def_QueueingFundamentals_Foundations_MarkovChain
import Definitions.Def_QueueingFundamentals_GM1_EmbeddedChain
import Definitions.Def_QueueingFundamentals_GM1_WaitingTime
import Definitions.Def_KendallQueues_GIMs_Model

open MeasureTheory Filter Topology
open QueueingFundamentals.Foundations QueueingFundamentals.GM1

namespace KendallQueues.GIMs

/-- Theorem IV, p. 350: when `ρ < 1`, in the limiting distribution `π` of the imbedded chain,
`Q` given `Q > 0` has the geometric law `(1 - λ) λ^{Q-1}` (`Q = 1, 2, …`) (23), and `w` given
`w > 0` is negative-exponential with mean `c = b/(s(1 - λ))` (24)–(25); both conditioning events
have positive probability. -/
theorem theorem4_conditional_laws (s : ℕ) (hs : 1 ≤ s) (A : Measure ℝ) (a b : ℝ) (ha : 0 < a)
    (hb : 0 < b) (hA : IsInterarrivalLaw A a⁻¹) (hρ : rho s a b < 1)
    (P : TransitionMatrix) (hP : P.p = gimsMatrix s A b)
    (lam : ℝ) (hlam : lam ∈ Set.Ioo (0 : ℝ) 1) (hF : F s A b lam = lam) :
    ∃ π : ℕ → ℝ, HasSum π 1 ∧
      (∀ i j, Tendsto (fun n => P.stepProb n i j) atTop (𝓝 (π j))) ∧
      (queueLaw s π 0 < 1 ∧
        ∀ n : ℕ, 1 ≤ n → queueLaw s π n = (1 - queueLaw s π 0) * ((1 - lam) * lam ^ (n - 1))) ∧
      (waitCDF s b π 0 < 1 ∧
        ∀ t : ℝ, 0 ≤ t →
          1 - waitCDF s b π t =
            (1 - waitCDF s b π 0) * Real.exp (-t / (b / (s * (1 - lam))))) := by sorry

end KendallQueues.GIMs
