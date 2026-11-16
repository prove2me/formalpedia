-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_joint_coherent_pool_bound
-- name    : InfoLossLAR.WorstCase.RegevSketch.joint_coherent_pool_bound
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T09:11:18.423701+00:00
-- url     : https://prove2.me/theorems/b91eacd1-e5e0-4fa3-aa0e-ae7d30de1c9f
-- title:
--   Joint quantum output error under reuse of one sample pool
-- statement:
--   Let $\Omega$ be a finite probability space and let a normalized quantum state evolve through $m$ isometries. For each stored sample $\omega$, suppose the actual sequence of isometries may depend on that same sample at every step; the ideal sequence is independent of $\omega$. Let $\psi_i$ be the ideal state after the first $i$ steps. Assume the average squared norm of the step error at $\psi_i$ is at most $2\varepsilon_i$. For every event $F$ on the complete measured register, the averaged absolute difference in its Born probability between the actual and ideal final states is bounded by
--
--   $$
--   \mathbb{E}_{\omega}\left[\left|\Pr_{\mathrm{actual},\omega}(F)-\Pr_{\mathrm{ideal}}(F)\right|\right]\le 4\sum_{i=0}^{m-1}\sqrt{\varepsilon_i}.
--   $$
--
--   The event may couple all output and garbage registers, and the same sample may be reused across steps. This abstract estimate is a reusable error bound for coherent DGS reductions; it does not assert that an actual DGS circuit satisfies the hypotheses.
--
--   **Formalization Note.** The state space is finite-dimensional complex Euclidean space; the hypotheses impose the squared norm bound on each ideal prefix rather than on the actual sample-dependent query state.
-- source:
--   Oded Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, https://cims.nyu.edu/~regev/papers/qcrypto.pdf, Lemmas 3.3 and 3.14, pp. 19 and 26 (PDF pages 19 and 26). This generic finite-dimensional ideal-prefix hybrid estimate is an explicit formalization aid, not a verbatim result or a construction of the algorithms in the source.

import Definitions.Def_RegevJointHybrid
set_option autoImplicit false
open scoped BigOperators
open RegevJointHybrid

namespace InfoLossLAR.WorstCase.RegevSketch

theorem joint_coherent_pool_bound {Ω α : Type*} [Fintype Ω] [Fintype α]
    (pool : Ω → ℝ) (hpool : ∀ sample,0 ≤ pool sample)
    (hmass : ∑ sample,pool sample=1)
    (actual : Ω → ℕ → EuclideanSpace ℂ α →ₗᵢ[ℂ] EuclideanSpace ℂ α)
    (ideal : ℕ → EuclideanSpace ℂ α →ₗᵢ[ℂ] EuclideanSpace ℂ α)
    (count : ℕ) (state : EuclideanSpace ℂ α) (hstate : ‖state‖=1)
    (event : α → Prop) (failure : ℕ → ℝ)
    (hstep : ∀ index<count,
      (∑ sample,pool sample*
        ‖actual sample index (evolve ideal index state)-ideal index (evolve ideal index state)‖^2) ≤
          2*failure index) :
    (∑ sample,pool sample*|bornEvent event (evolve (actual sample) count state)-
      bornEvent event (evolve ideal count state)|) ≤
      ∑ index ∈ Finset.range count,4*Real.sqrt (failure index) := by sorry

end InfoLossLAR.WorstCase.RegevSketch
