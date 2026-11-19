-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_recursive_successful_request_bounds
-- name    : NearlyOptimalPPR.Computation.recursive_successful_request_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:05:20.925295+00:00
-- url     : https://prove2.me/theorems/9eee1b37-1b68-40c3-8181-db9afe4d9fa1
-- title:
--   Residual scale and density at a requested full solve
-- statement:
--   Consider a full solve requested after a successful episode return in Algorithms 6–9. Let $q_j$ and $b_j$ be its threshold and block size, $H_j$ its active domain, and $\mu_j=\sum_{v\in H_j}r_j(v)$ its residual mass. At that full-solve state,
--
--   $$q_jb_j<2\mu_j,\qquad
--   r_j(v)\le\frac{2\kappa_0\mu_j}{b_j}d_v\quad(v\in H_j).$$
--
--   The graph is finite and undirected with a nonisolated seed, $0<\alpha<1$, and a positive root threshold. The successful-return instruction occurs two operational states before the full solve; the intervening entry preserves the domain, residual, threshold and block size.
--
--   These are the scale and density premises used in Lemma 5.8 to distinguish mass-halving solves from exceptional solves.
-- source:
--   Li, Xu, Yang, Zhou, Nearly optimal Personalized PageRank computation, STOC 2027 submission #884, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/884.pdf, Lemmas 5.7–5.8 and their proof pp.26–28; Lemma 4.4 p.18 and finite-prefix counts pp.28–29.

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
open Finset Matrix NearlyOptimalPPR.Computation

theorem NearlyOptimalPPR.Computation.recursive_successful_request_bounds (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t id : ℕ)
    (he : fullSolveEvent g (recursiveRun m g s α q ℓ schedule t) id)
    (hfinish : currentPC (recursiveRun m g s α q ℓ schedule (t-2))=.finishEpisode) :
    let st := recursiveRun m g s α q ℓ schedule t
    (st.frames st.top).q*(st.frames st.top).block < 2*(∑ v ∈ (st.frames st.top).active, (st.frames st.top).residual v) ∧
      ∀ v ∈ (st.frames st.top).active, (st.frames st.top).residual v ≤
        (kappa ℓ 0 : ℝ)*(2*(∑ w ∈ (st.frames st.top).active, (st.frames st.top).residual w)/(st.frames st.top).block)*
          LocalPush.deg g.graph v := by sorry
