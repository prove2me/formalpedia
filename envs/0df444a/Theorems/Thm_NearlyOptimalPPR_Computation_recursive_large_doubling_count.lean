-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_recursive_large_doubling_count
-- name    : NearlyOptimalPPR.Computation.recursive_large_doubling_count
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:15:55.247063+00:00
-- url     : https://prove2.me/theorems/87a9ae38-e810-4551-8f84-18297156e63d
-- title:
--   Number of full solves with large potential-doubling volume
-- statement:
--   Let $\tau(0)<\cdots<\tau(T)$ be full-solve states of one recursive PageRank call. Suppose $E\subseteq\{0,\ldots,T-1\}$ selects solves whose doubling sets $D_i$ satisfy
--
--   $$\operatorname{vol}(D_i)\ge\frac{b}{64\kappa_0}.$$
--
--   Then
--
--   $$|E|\le\frac{384\kappa_0N}{b}\,\frac{\log(2/q)}{\log2}.$$
--
--   Here $q$ is the root threshold with $0<q\le1$, $N,b$ are the call's initial scale and block size, and $\kappa_0=\ell+3$. The finite undirected graph has a nonisolated seed and $0<\alpha\le1/2$.
--
--   This count combines the weighted doubling bound with the volume bound of the active domain. It controls the potential-doubling exceptions in the finite-prefix proof of Lemma 4.4.
-- source:
--   Li, Xu, Yang, Zhou, Nearly optimal Personalized PageRank computation, STOC 2027 submission #884, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/884.pdf, Lemmas 5.7–5.8 pp.26–28 and the finite-prefix event-counting proof of Lemma 4.4 pp.28–29; Lemma 4.4 statement p.18.

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
open Finset Matrix NearlyOptimalPPR.Computation

theorem NearlyOptimalPPR.Computation.recursive_large_doubling_count (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α ≤ 1/2) (hq : 0 < q ∧ q ≤ 1) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (τ : ℕ → ℕ) (hτ : StrictMono τ) (T id : ℕ)
    (hfull : ∀ i ≤ T, fullSolveEvent g (recursiveRun m g s α q ℓ schedule (τ i)) id)
    (E : Finset ℕ) (hE : E ⊆ Finset.range T) :
    let run := recursiveRun m g s α q ℓ schedule
    let st := run (τ 0)
    let j := st.top
    (∀ i ∈ E, ((st.frames j).block : ℝ)/(64*(kappa ℓ 0 : ℝ)) ≤
      (volumeNat g (fullSolveDoubles g α (run (τ i)) j) : ℝ)) →
      (E.card : ℝ) ≤ 384*(kappa ℓ 0 : ℝ)*(st.frames j).N*
        (Real.log (2/q)/Real.log 2)/(st.frames j).block := by sorry
