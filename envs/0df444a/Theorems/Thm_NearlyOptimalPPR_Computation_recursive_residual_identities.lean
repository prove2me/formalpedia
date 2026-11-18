-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_recursive_residual_identities
-- name    : NearlyOptimalPPR.Computation.recursive_residual_identities
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T05:30:55.306496+00:00
-- url     : https://prove2.me/theorems/1cfb9232-2532-4cd9-8efc-64007817aa4d
-- title:
--   Residual identities on every recursive execution prefix
-- statement:
--   Let $G$ be a finite graph with source $s$. For any real teleportation parameter $\alpha$, initial threshold $q$, recursion depth $\ell$, block schedule, and finite execution prefix of Algorithms 6–9, the active regions and queues lie in their prescribed nested domains. The root frame keeps threshold $q$ and satisfies
--
--   $$e_s-[D-(1-\alpha)A]x=r_0+D\bigl(q\mathbf1_{H_0}+4x\mathbf1_{V\setminus H_0}\bigr).$$
--
--   For each adjacent pair of open frames, let $y_{j+1}$ denote the child's relative potential. On the parent's active region,
--
--   $$r_j(v)=r_{j+1}(v)+d_v\begin{cases}q_{j+1},&v\in H_{j+1},\\4y_{j+1}(v),&v\notin H_{j+1}.\end{cases}$$
--
--   These are exact preservation identities of the transition system, valid before termination and independently of positivity restrictions. Their principal use is to transfer residual bounds between levels and relate the root potential to PageRank.
-- source:
--   Li, Xu, Yang, Zhou, Nearly optimal Personalized PageRank computation, STOC 2027 submission #884 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/884.pdf, equation (1) p.6, equation (4) p.17 and Algorithms 6–9 pp.20–22; finite-prefix invariants used in Lemmas 3.7 and 4.3.

import Definitions.Def_NearlyOptimalPPR_Computation_proof_invariants
set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
noncomputable section

theorem NearlyOptimalPPR.Computation.recursive_residual_identities (m : SolveModel) (n : ℕ) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    let st := recursiveRun m g s α q ℓ schedule t
    RegionInvariant st ∧ RootIdentity g s α st ∧ LayerIdentity g st ∧ (st.frames 0).q = q := by sorry
