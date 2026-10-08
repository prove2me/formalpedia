-- Prove2me | Theorems.Thm_GittinsDAI_IndexTheorem_dai_theorem
-- name    : GittinsDAI.IndexTheorem.dai_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T10:26:37.607538+00:00
-- url     : https://prove2.me/theorems/fdc20ffe-2863-42d2-92a5-57a48f7df663
-- title:
--   The DAI Theorem — a policy is optimal iff it almost surely continues a bandit process of maximal index at every stage
-- statement:
--   Consider a **simple family of $k$ alternative bandit processes**. Each process is a Markov chain on a common standard Borel state space $\Theta$ with transition kernel $P$ and measurable reward function $R$. At each stage $n=0,1,2,\dots$ a policy observes the history so far (the past state vectors and the processes chosen) and the current state vector $(x_1,\dots,x_k)$, and selects one process, possibly at random; the selected process $i$ earns $a^n R(x_i)$ and moves according to $P$, while the other processes are frozen. Policies may be randomized and history-dependent. The discount factor satisfies $0<a<1$, and for every state $x$
--   $$E\Big\{\sum_{t=0}^{\infty} a^t |R(x(t))| \,\Big|\, x(0)=x\Big\}<\infty .$$
--   Write $V_\pi(x)$ for the total expected discounted reward of a policy $\pi$ from the initial state vector $x$, and $\nu(y)$ for the dynamic allocation index (Eq. (2)) of a process in state $y$. Assume that $\nu$ is a measurable function of the state, as the paper asserts on p. 151.
--
--   **The DAI Theorem.** For every policy $\pi$ and every initial state vector $x$,
--   $$V_\pi(x) = \sup_{\pi'} V_{\pi'}(x)$$
--   if and only if, at every stage $n$ and for almost every history of the first $n$ stages under the law of play of $\pi$ from $x$, the process selected by $\pi$ is, with probability one, one of those whose index in its current state is maximal:
--   $$\pi_n\big(\{i : \nu(x_i(n)) = \max_j \nu(x_j(n))\} \,\big|\, \text{history}\big) = 1 .$$
--
--   In words: for a simple family of alternative bandit processes a policy is optimal if and only if at each stage the bandit process selected for continuation is almost always one of those whose dynamic allocation index is then maximal. The theorem reduces the $k$-process allocation problem to the computation of an index for each process separately. Its "if" half is the Gittins index theorem.
--
--   **Formalization Note** The model is the published discounted $k$-armed Markov bandit (`MarkovBanditPolicy`, `markovBanditMeasure`, `markovBanditDiscountedValue`, `gittinsIndex`). "Optimal" means attaining the supremum over all policies from the given initial state vector; the supremum is a real `iSup`, which is finite here because each process's discounted absolute reward is integrable, so the values are bounded uniformly in the policy. "At each stage … almost always" is read per stage, almost surely under the policy's own law from $x$; it is weaker than requiring the index rule on every history. All processes share one kernel and one reward function; a family of different processes is encoded on the disjoint union of their state spaces. The paper's standing assumption that the supremum of the total expected reward is finite is read as the integrability hypothesis above, and the measurability of the index is an explicit hypothesis. The paper's state space only needs measurable singletons; the Lean asks for a standard Borel space.
-- source:
--   Gittins, Bandit Processes and Dynamic Allocation Indices, J. R. Statist. Soc. B 41 (1979), p. 154, The DAI Theorem (Section 3)

import Mathlib
import Definitions.Def_GittinsIndex
import Definitions.Def_AllocationIndices_Index
open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace GittinsDAI.IndexTheorem

/-- **The DAI Theorem** (Gittins 1979, Section 3, p. 154): for a simple family of alternative
bandit processes, a policy is optimal if and only if at each stage the bandit process selected
for continuation is almost always one of those whose dynamic allocation index is then maximal.

"Optimal" = attains the supremum of the total expected discounted reward over all (randomized,
history-dependent) policies from the initial state vector `x`; "at each stage … almost always" =
for every round `n`, for almost every history of the first `n` rounds under the policy's own law
from `x`, the selection kernel puts mass `1` on the arms of maximal Gittins index. The
measurability of the index (asserted by the paper on p. 151) is the hypothesis `hg`. -/
theorem dai_theorem {k : ℕ} {S : Type*} [MeasurableSpace S] [StandardBorelSpace S]
    (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hint : DiscountedRewardIntegrable P r α)
    (hg : Measurable (gittinsIndex P r α))
    (π : MarkovBanditPolicy k S) (x : Fin k → S) :
    markovBanditDiscountedValue P r α π x =
        ⨆ π' : MarkovBanditPolicy k S, markovBanditDiscountedValue P r α π' x ↔
      ∀ n : ℕ, ∀ᵐ h ∂(markovBanditMeasure P π x n),
        (π.select n) h {a | ∀ j, gittinsIndex P r α (h.2 j) ≤ gittinsIndex P r α (h.2 a)} = 1 := by sorry

end GittinsDAI.IndexTheorem
