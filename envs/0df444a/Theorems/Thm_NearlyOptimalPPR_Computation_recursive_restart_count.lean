-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_recursive_restart_count
-- name    : NearlyOptimalPPR.Computation.recursive_restart_count
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:19:06.084793+00:00
-- url     : https://prove2.me/theorems/6c9ad9b2-b2d9-48c0-be3f-11743a92ba03
-- title:
--   Number of budget-restart full solves in a PageRank call
-- statement:
--   Let $\tau(0)<\cdots<\tau(T)$ be finite full-solve states of one recursive PageRank call. Let $E\subseteq\{0,\ldots,T-1\}$ contain only transitions for which the next full solve was requested by a budget restart. If $N$ and $b$ are the call's scale and block size at the first snapshot, then
--
--   $$|E|\le\frac{2\kappa_0N}{b},\qquad \kappa_0=\ell+3.$$
--
--   The input graph is finite and undirected with a nonisolated seed, $0<\alpha<1$, and positive root threshold. Each full solve is a reachable permitted event of that same call; no termination hypothesis is imposed.
--
--   This is the budget-restart count used in Lemma 4.4. It separates restarts from the other exceptions to residual-mass descent.
-- source:
--   Li, Xu, Yang, Zhou, Nearly optimal Personalized PageRank computation, STOC 2027 submission #884, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/884.pdf, Lemmas 5.7–5.8 pp.26–28 and the finite-prefix event-counting proof of Lemma 4.4 pp.28–29; Lemma 4.4 statement p.18.

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
open Finset Matrix NearlyOptimalPPR.Computation

theorem NearlyOptimalPPR.Computation.recursive_restart_count (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (τ : ℕ → ℕ) (hτ : StrictMono τ) (T id : ℕ)
    (hfull : ∀ i ≤ T, fullSolveEvent g (recursiveRun m g s α q ℓ schedule (τ i)) id)
    (E : Finset ℕ) (hE : E ⊆ Finset.range T)
    (hrestart : ∀ i ∈ E, currentPC (recursiveRun m g s α q ℓ schedule (τ (i+1)-2))=.restartDrain) :
    let st := recursiveRun m g s α q ℓ schedule (τ 0)
    (E.card : ℝ) ≤ 2*(kappa ℓ 0 : ℝ)*(st.frames st.top).N/(st.frames st.top).block := by sorry
