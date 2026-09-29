-- Prove2me | Theorems.Thm_MarkovChainCLT_partialTraj_succ_self_apply_eq_map
-- name    : MarkovChainCLT.partialTraj_succ_self_apply_eq_map
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T19:59:33.893921+00:00
-- url     : https://prove2.me/theorems/466f93a1-7e27-4192-957f-a0ddfc6fa8ab
-- title:
--   One step of the trajectory kernel is an explicit pushforward of $P$
-- statement:
--   Let $P$ be a Markov transition kernel on $\mathsf{X}$ and let $\kappa_n$ be the associated time-homogeneous one-step family used by the Ionescu–Tulcea construction, $\kappa_n(\omega,\cdot) = P(\omega_n,\cdot)$. For every $m$ and every partial trajectory $v = (v_0,\dots,v_m)$,
--
--   $$\mathrm{partialTraj}_{\kappa}(m, m+1)(v) \;=\; P(v_m, \cdot) \circ \Bigl(w \mapsto (v, w)\Bigr)^{-1},$$
--
--   i.e. **extending a trajectory by one time step is the pushforward of $P(v_m,\cdot)$ along the map that appends $w$ as the new last coordinate**, glueing the block $\mathrm{Iic}\,m$ with the singleton block $\mathrm{Ioc}\,m\,(m+1)$.
--
--   **Why this is worth isolating.** In Mathlib the one-step extension `partialTraj κ m (m+1)` is *defined* as
--   $$\bigl(\mathrm{id} \times_{\mathrm{k}} (\kappa_m)_*\mathrm{piSingleton}_m\bigr)_*\,\mathrm{IicProdIoc}_{m,m+1},$$
--   a composite of a product kernel, a kernel pushforward, and a gluing map between dependent function types indexed by `Finset.Iic` and `Finset.Ioc`. That form is well suited to the abstract development, but it is unusable for hands-on computation: every concrete manipulation has to unfold the product kernel, discharge the measurability of the gluing map, and fight the dependent indexing.
--
--   This lemma performs that unfolding once and delivers the elementary description that any concrete argument actually wants: *a single pushforward of $P$ along an explicit map*. Two things become immediate from it:
--
--   * the one-step law depends on $v$ **only through its last coordinate $v_m$** — this is precisely the Markov property, which is invisible in the definitional form;
--   * the transition kernel is **the same $P$ for every $m$** — time-homogeneity, which the general `Kernel.traj` API deliberately does not know, since it is built for possibly time-inhomogeneous families.
--
--   Both facts are exactly what is needed to prove that shifting a trajectory by one time step is the same as taking one step of $P$ and then running the chain, and hence to establish stationarity of the chain started from an invariant measure, the Markov property on path space, and the mixing-coefficient estimates that depend on it.
--
--   **Proof.** Unfold `partialTraj_succ_self`, evaluate the product kernel at $v$ (the first factor is `Kernel.id`, so it contributes the Dirac mass $\delta_v$), and use `Measure.dirac_prod` to rewrite $\delta_v \otimes \nu$ as the pushforward of $\nu$ along $w \mapsto (v,w)$. Composing the three pushforwards with `Measure.map_map` and observing $\kappa_m(v) = P(v_m,\cdot)$ by definition gives the claim definitionally.
-- source:
--   C. T. Ionescu Tulcea, "Mesures dans les espaces produits", Atti Accad. Naz. Lincei Rend. 7 (1949) 208-211; J. Neveu, Mathematical Foundations of the Calculus of Probability, Holden-Day 1965, Ch. V; S. P. Meyn and R. L. Tweedie, Markov Chains and Stochastic Stability, 2nd ed., Cambridge 2009, Ch. 3.

import Definitions.Def_MarkovChainPathMeasure

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder ProbabilityTheory
open scoped ENNReal NNReal Topology

theorem MarkovChainCLT.partialTraj_succ_self_apply_eq_map {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (m : ℕ) (v : Π _i : Finset.Iic m, S) :
    Kernel.partialTraj (X := fun _ : ℕ => S) (BanditAlgorithm.markovChainStep P) m (m + 1) v
      = (P (v ⟨m, Finset.mem_Iic.2 le_rfl⟩)).map
          (fun w => IicProdIoc (X := fun _ : ℕ => S) m (m + 1)
            (v, MeasurableEquiv.piSingleton (X := fun _ : ℕ => S) m w)) := by sorry
