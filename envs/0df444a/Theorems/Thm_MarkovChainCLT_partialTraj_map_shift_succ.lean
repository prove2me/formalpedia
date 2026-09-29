-- Prove2me | Theorems.Thm_MarkovChainCLT_partialTraj_map_shift_succ
-- name    : MarkovChainCLT.partialTraj_map_shift_succ
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T20:05:38.183797+00:00
-- url     : https://prove2.me/theorems/160a19bf-e32e-46b0-bb73-ca852ab89ddf
-- title:
--   Time-homogeneity: the shift commutes with one-step extension of a trajectory
-- statement:
--   Let $P$ be a Markov kernel on $\mathsf{X}$ and write $\sigma$ for the *shift on initial segments*, the map $\mathrm{Iic}(m{+}1) \to \mathrm{Iic}(m)$ given by $(\sigma v)_i = v_{i+1}$, which drops the first coordinate of a partial trajectory. Then for every $n$ and every $u = (u_0,\dots,u_{n+1})$,
--
--   $$\sigma_*\bigl[\mathrm{partialTraj}(n{+}1,\,n{+}2)(u)\bigr] \;=\; \mathrm{partialTraj}(n,\,n{+}1)\bigl(\sigma u\bigr).$$
--
--   In words: **extending a trajectory by one step and then dropping its first coordinate is the same as dropping the first coordinate and then extending.** The shift commutes with one-step extension.
--
--   **Why it is the crux.** This is the exact formal content of time-homogeneity, and it is where the two structural facts about the constant one-step family are actually consumed:
--
--   * *Markov property.* The one-step extension of $u$ uses the kernel $P(u_{n+1},\cdot)$, while the one-step extension of $\sigma u$ uses $P\bigl((\sigma u)_n,\cdot\bigr)$. These are the same kernel because $(\sigma u)_n = u_{n+1}$ — the shift preserves the last coordinate, which is the only thing the transition law depends on.
--   * *Time-homogeneity.* The kernel used at time $n+1$ and the kernel used at time $n$ are both $P$. For a general, possibly time-inhomogeneous family $\kappa_n$ the statement is simply false: one would be comparing $\kappa_{n+1}$ with $\kappa_n$.
--
--   Once the two transition kernels are identified, what remains is a purely combinatorial identity between the two gluing maps: appending a new coordinate at position $n+2$ and then shifting, versus shifting and then appending at position $n+1$. Both produce the function on $\mathrm{Iic}(n{+}1)$ equal to $u_{i+1}$ for $i \le n$ and to the new coordinate at $i = n+1$.
--
--   **Where it leads.** Iterating this identity along the `partialTraj` recursion `partialTraj(0, n{+}1) = partialTraj(n, n{+}1) \circ partialTraj(0, n)` propagates the shift through all finite-dimensional marginals of the trajectory law. Combined with the fact that a path measure is determined by those marginals, it yields the global statement that shifting a trajectory by one time step is the same as taking one step of $P$ and then running the chain — the identity underlying stationarity of a chain started from an invariant measure, the Markov property on path space, and every mixing-coefficient estimate that rests on it.
--
--   **Proof.** Rewrite both sides with the explicit pushforward description of a one-step extension, so each becomes a pushforward of a single measure $P(u_{n+1},\cdot)$ along an explicit gluing map. Composing the pushforwards reduces the claim to the pointwise identity between the two maps, which is settled by splitting on whether the index $i$ satisfies $i \le n$: in the first case both sides read off $u_{i+1}$, in the second both return the newly drawn coordinate (using that for a constant family the singleton-block identification is the constant map).
-- source:
--   C. T. Ionescu Tulcea, "Mesures dans les espaces produits", Atti Accad. Naz. Lincei Rend. 7 (1949) 208-211; J. Neveu, Mathematical Foundations of the Calculus of Probability, Holden-Day 1965, Ch. V; S. P. Meyn and R. L. Tweedie, Markov Chains and Stochastic Stability, 2nd ed., Cambridge 2009, Ch. 3.

import Definitions.Def_MarkovChainPathMeasure

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder ProbabilityTheory
open scoped ENNReal NNReal Topology

theorem MarkovChainCLT.partialTraj_map_shift_succ {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (n : ℕ) (u : Π _j : Finset.Iic (n + 1), S) :
    (Kernel.partialTraj (X := fun _ : ℕ => S) (BanditAlgorithm.markovChainStep P)
        (n + 1) (n + 1 + 1) u).map
        (fun v i => v ⟨i.1 + 1, Finset.mem_Iic.2 (Nat.succ_le_succ (Finset.mem_Iic.mp i.2))⟩)
      = Kernel.partialTraj (X := fun _ : ℕ => S) (BanditAlgorithm.markovChainStep P) n (n + 1)
          (fun i => u ⟨i.1 + 1, Finset.mem_Iic.2 (Nat.succ_le_succ (Finset.mem_Iic.mp i.2))⟩) := by sorry
