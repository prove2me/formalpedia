-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_recursive_large_input_count
-- name    : NearlyOptimalPPR.Computation.recursive_large_input_count
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:15:44.803342+00:00
-- url     : https://prove2.me/theorems/5dd3e3a1-dc6f-4d7c-bd23-d8709af2e1e2
-- title:
--   Number of full solves with large incoming or activation charge
-- statement:
--   Let $\tau(0)<\cdots<\tau(T)$ be full-solve states of one recursive call, with initial threshold $q_j$, scale $N$ and block size $b$. For consecutive snapshots define
--
--   $$J_i=\sum_{\tau(i)+1\le k<\tau(i+1)}I_j(k)
--   +4\kappa_0q_j\operatorname{vol}\bigl(H_j(\tau(i+1))\setminus H_j(\tau(i))\bigr).$$
--
--   If $E\subseteq\{0,\ldots,T-1\}$ and $J_i\ge q_jb/8$ for every $i\in E$, then
--
--   $$|E|\le\frac{80\kappa_0N}{b}.$$
--
--   Here $I_j$ is charged exterior-push inflow and $\kappa_0=\ell+3$. The finite undirected graph has a nonisolated seed, $0<\alpha<1$, and positive root threshold. This finite-prefix estimate pays for one class of exceptional full solves in Lemma 4.4.
-- source:
--   Li, Xu, Yang, Zhou, Nearly optimal Personalized PageRank computation, STOC 2027 submission #884, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/884.pdf, Lemmas 5.7–5.8 pp.26–28 and the finite-prefix event-counting proof of Lemma 4.4 pp.28–29; Lemma 4.4 statement p.18.

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
open Finset Matrix NearlyOptimalPPR.Computation

theorem NearlyOptimalPPR.Computation.recursive_large_input_count (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (τ : ℕ → ℕ) (hτ : StrictMono τ) (T id : ℕ)
    (hfull : ∀ i ≤ T, fullSolveEvent g (recursiveRun m g s α q ℓ schedule (τ i)) id)
    (E : Finset ℕ) (hE : E ⊆ Finset.range T) :
    let run := recursiveRun m g s α q ℓ schedule
    let st := run (τ 0)
    let j := st.top
    (∀ i ∈ E, (st.frames j).q*(st.frames j).block/8 ≤ fullPairInput g α ℓ run j τ i) →
      (E.card : ℝ) ≤ 80*(kappa ℓ 0 : ℝ)*(st.frames j).N/(st.frames j).block := by sorry
