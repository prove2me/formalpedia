-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_recursive_full_solve_comparison
-- name    : NearlyOptimalPPR.Computation.recursive_full_solve_comparison
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:05:28.195585+00:00
-- url     : https://prove2.me/theorems/c477c402-3792-4196-8a6f-37a2336865d9
-- title:
--   Residual comparison between full-solve snapshots
-- statement:
--   Let $a$ be a permitted full-solve state of open level $j$, and let $b\ge a+1$ be a later state throughout which that level remains open. Assume the full solve starts with no pending exterior push and no exhausted open budget. Write $H=H_j(a)$, $F=H_j(b)$, $Z=F\setminus H$, and let $h$ be the exact solve on $H$ with source $r_j(a)$. If $y_j(a)$ is the virtual potential, put $D=\{v\in H:h(v)>y_j(a,v)\}$ and $u=x(b)-x(a+1)$. Then
--
--   $$\sum_{v\in F}r_j(b,v)\le
--   (1-\alpha)\sum_{v\notin F}d_vu_v
--   +4\kappa_0q_j\operatorname{vol}(Z)
--   +2\kappa_0q_j\operatorname{vol}(D)
--   +2\sum_{v\in D}r_j(a,v).$$
--
--   Here $q_j$ is the threshold at the initial snapshot and $\kappa_0=\ell+3$. The finite undirected input has a nonisolated seed, $0<\alpha<1$, and positive root threshold.
--
--   This is the exact-solve specialization of the comparison behind Lemma 5.7. Its right-hand side separates later exterior flow, newly activated volume, and vertices whose potential doubles.
-- source:
--   Li, Xu, Yang, Zhou, Nearly optimal Personalized PageRank computation, STOC 2027 submission #884, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/884.pdf, Lemmas 5.7–5.8 and their proof pp.26–28; Lemma 4.4 p.18 and finite-prefix counts pp.28–29.

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
open Finset Matrix NearlyOptimalPPR.Computation

theorem NearlyOptimalPPR.Computation.recursive_full_solve_comparison (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (a b : ℕ) (hab : a+1 ≤ b) :
    let run := recursiveRun m g s α q ℓ schedule
    let st := run a
    let next := run b
    let j := st.top
    let H := (st.frames j).active
    let F := (next.frames j).active
    let Z := F \ H
    let h := solveOn g α H (st.frames j).residual
    let u := next.x-(run (a+1)).x
    let D := doubledSet H h (virtualPotential st j)
    (∀ k, a ≤ k → k < b → j ≤ (run k).top) → j ≤ next.top →
    st.done = false → ¬componentComplete st → (st.frames j).pc = .fullSolve →
      ¬anyExhausted st → pendingPush st = none →
      (∑ v ∈ F, (next.frames j).residual v) ≤
        (1-α)*(∑ v ∈ Fᶜ, LocalPush.deg g.graph v*u v)+
        4*(kappa ℓ 0 : ℝ)*(st.frames j).q*(volumeNat g Z : ℝ)+
        2*(kappa ℓ 0 : ℝ)*(st.frames j).q*(volumeNat g D : ℝ)+
        2*∑ v ∈ D, (st.frames j).residual v := by sorry
