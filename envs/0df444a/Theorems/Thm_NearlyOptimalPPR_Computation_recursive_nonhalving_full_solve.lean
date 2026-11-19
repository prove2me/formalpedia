-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_recursive_nonhalving_full_solve
-- name    : NearlyOptimalPPR.Computation.recursive_nonhalving_full_solve
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:15:56.270528+00:00
-- url     : https://prove2.me/theorems/c3b0b85b-a440-41d1-b964-30435e055531
-- title:
--   Classification of a full solve that fails to halve residual mass
-- statement:
--   Consider full solves $a<b$ of one recursive call, where the solve at $a$ was requested after a successful episode return. Write $H$ and $F$ for the active domains at these snapshots, $\mu$ and $\mu_{\mathrm{next}}$ for their residual masses, and $D$ for the vertices whose virtual potential more than doubles in the solve at $a$. Put
--
--   $$J=\sum_{a+1\le k<b}I_j(k)+4\kappa_0q_j\operatorname{vol}(F\setminus H).$$
--
--   If $\mu_{\mathrm{next}}\ge\mu/2$, then
--
--   $$J\ge\mu/4\quad\text{or}\quad
--   \operatorname{vol}(D)>\frac{b}{64\kappa_0}.$$
--
--   The quantities $q_j,b$ are the initial call threshold and block size, and $\kappa_0=\ell+3$. The graph is finite and undirected with a nonisolated seed, $0<\alpha<1$, and positive root threshold.
--
--   This is the exact-solve finite-prefix form of Lemma 5.8: failure of mass halving is paid for either by substantial incoming/discovery charge or by substantial potential doubling.
-- source:
--   Li, Xu, Yang, Zhou, Nearly optimal Personalized PageRank computation, STOC 2027 submission #884, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/884.pdf, Lemmas 5.7–5.8 pp.26–28 and the finite-prefix event-counting proof of Lemma 4.4 pp.28–29; Lemma 4.4 statement p.18.

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
open Finset Matrix NearlyOptimalPPR.Computation

theorem NearlyOptimalPPR.Computation.recursive_nonhalving_full_solve (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b id : ℕ) (hab : a < b)
    (ha : fullSolveEvent g (recursiveRun m g s α q ℓ schedule a) id)
    (hb : fullSolveEvent g (recursiveRun m g s α q ℓ schedule b) id)
    (hf : currentPC (recursiveRun m g s α q ℓ schedule (a-2))=.finishEpisode) :
    let run := recursiveRun m g s α q ℓ schedule
    let j := (run a).top
    let H := ((run a).frames j).active
    let F := ((run b).frames j).active
    let μ := ∑ v ∈ H, ((run a).frames j).residual v
    let μnext := ∑ v ∈ F, ((run b).frames j).residual v
    let J := (∑ k ∈ Finset.range (b-(a+1)), incomingProduction g α (run (a+1+k)) j)+
      4*(kappa ℓ 0 : ℝ)*((run a).frames j).q*(volumeNat g (F \ H) : ℝ)
    μ/2 ≤ μnext → μ/4 ≤ J ∨
      (((run a).frames j).block : ℝ)/(64*(kappa ℓ 0 : ℝ)) <
        (volumeNat g (fullSolveDoubles g α (run a) j) : ℝ) := by sorry
