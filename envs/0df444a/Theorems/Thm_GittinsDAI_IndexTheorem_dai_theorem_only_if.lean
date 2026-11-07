-- Prove2me | Theorems.Thm_GittinsDAI_IndexTheorem_dai_theorem_only_if
-- name    : GittinsDAI.IndexTheorem.dai_theorem_only_if
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-06T17:58:50.57912+00:00
-- url     : https://prove2.me/theorems/d572317b-e5a8-4599-bd39-864e94bc0742
-- title:
--   The DAI Theorem, "only if" half — an optimal policy almost surely continues a process of maximal index at every stage
-- statement:
--   Consider a **simple family of $k$ alternative bandit processes**. Each process is a Markov chain on a common standard Borel state space $\Theta$ with transition kernel $P$ and measurable reward function $R$. At each stage $n=0,1,2,\dots$ a policy observes the history so far (the past state vectors and the processes chosen) and the current state vector $(x_1,\dots,x_k)$, and selects one process, possibly at random; the selected process $i$ earns $a^n R(x_i)$ and moves according to $P$, while the other processes are frozen. Policies may be randomized and history-dependent. The discount factor satisfies $0<a<1$, and for every state $x$
--   $$E\Big\{\sum_{t=0}^{\infty} a^t |R(x(t))| \,\Big|\, x(0)=x\Big\}<\infty .$$
--   Write $V_\pi(x)$ for the total expected discounted reward of a policy $\pi$ from the initial state vector $x$, and $\nu(y)$ for the dynamic allocation index (Eq. (2)) of a process in state $y$, assumed to be a measurable function of the state (as the paper asserts on p. 151).
--
--   **The DAI Theorem, "only if" half.** Let $\pi$ be a policy and $x$ an initial state vector with
--   $$V_\pi(x) = \sup_{\pi'} V_{\pi'}(x).$$
--   Then at every stage $n$, for almost every history of the first $n$ stages under the law of play of $\pi$ from $x$, the process selected by $\pi$ is, with probability one, one of those whose index in its current state is maximal:
--   $$\pi_n\big(\{i : \nu(x_i(n)) = \max_j \nu(x_j(n))\} \,\big|\, \text{history}\big) = 1 .$$
--
--   This is the necessity half of Gittins' DAI Theorem ("a policy is optimal if and only if at each stage the bandit process selected for continuation is almost always one of those whose dynamic allocation index is then maximal"): every optimal policy is, almost surely along its own trajectory, an index policy. The sufficiency half (an index policy is optimal) is the Gittins index theorem.
--
--   **Formalization Note** Same model and hypotheses as the full DAI theorem `GittinsDAI.IndexTheorem.dai_theorem` (`MarkovBanditPolicy`, `markovBanditMeasure`, `markovBanditDiscountedValue`, `gittinsIndex`). "Optimal" means attaining the (real) supremum over all policies from the given initial state vector $x$; "at each stage … almost always" is read per stage, almost surely under the policy's own finite-horizon law from $x$.
-- source:
--   Gittins, Bandit Processes and Dynamic Allocation Indices, J. R. Statist. Soc. B 41 (1979), p. 154, The DAI Theorem (Section 3), "only if" direction

import Mathlib
import Definitions.Def_GittinsIndex
import Definitions.Def_AllocationIndices_Index
open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace GittinsDAI.IndexTheorem

/-- **The DAI Theorem, "only if" half** (Gittins 1979, Section 3, p. 154): for a simple family of
alternative bandit processes, an optimal policy almost surely continues, at every stage, a bandit
process whose dynamic allocation index is then maximal. -/
theorem dai_theorem_only_if {k : ℕ} {S : Type*} [MeasurableSpace S] [StandardBorelSpace S]
    (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hint : DiscountedRewardIntegrable P r α)
    (hg : Measurable (gittinsIndex P r α))
    (π : MarkovBanditPolicy k S) (x : Fin k → S)
    (hopt : markovBanditDiscountedValue P r α π x =
        ⨆ π' : MarkovBanditPolicy k S, markovBanditDiscountedValue P r α π' x) :
    ∀ n : ℕ, ∀ᵐ h ∂(markovBanditMeasure P π x n),
        (π.select n) h {a | ∀ j, gittinsIndex P r α (h.2 j) ≤ gittinsIndex P r α (h.2 a)} = 1 := by sorry

end GittinsDAI.IndexTheorem
