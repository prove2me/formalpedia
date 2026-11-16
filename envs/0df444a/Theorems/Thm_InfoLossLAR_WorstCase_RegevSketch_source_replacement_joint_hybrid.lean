-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_source_replacement_joint_hybrid
-- name    : InfoLossLAR.WorstCase.RegevSketch.source_replacement_joint_hybrid
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T09:23:42.113551+00:00
-- url     : https://prove2.me/theorems/3e9e6daf-9a2a-49c9-8579-ce3c82e6052b
-- title:
--   Joint coherent hybrid bound with one initial-pool total-variation error
-- statement:
--   Let $P$ and $Q$ be probability laws on the same finite set of possible sample pools, with total variation at most $\delta$. Starting from a normalized quantum state, let each actual isometry depend on the same sampled pool at every step, while the ideal isometries are independent of that pool. Suppose that the average squared error of step $i$ at the ideal prefix, averaged over $Q$, is at most $2\varepsilon_i$. Then, for every event $F$ on the full measured register,
--
--   $$
--   \left|\mathbb E_{P}\Pr_{\mathrm{actual},\omega}[F]-\Pr_{\mathrm{ideal}}[F]\right|
--   \le \delta+4\sum_{i=0}^{m-1}\sqrt{\varepsilon_i}.
--   $$
--
--   The complete initial pool is replaced once, and the statement permits arbitrary dependence of all subsequent operations on that same pool. It supplies an error-composition interface for a finite reference approximation to an initial lattice Gaussian pool; it does not establish that approximation or construct the DGS steps.
--
--   **Formalization Note.** The finite-pool total variation assumption is stated as half of the sum of absolute weight differences. The final event can involve the entire register, including retained garbage.
-- source:
--   Oded Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, https://cims.nyu.edu/~regev/papers/qcrypto.pdf, Lemmas 3.2–3.3 and 3.14, pp. 18–19 and 26–27. This finite-pool source-replacement plus ideal-prefix hybrid bound is a separately derived formalization aid; it does not assert the quantum DGS construction or a verbatim theorem of the source.

import Definitions.Def_RegevJointHybrid
set_option autoImplicit false
open scoped BigOperators
open RegevJointHybrid

namespace InfoLossLAR.WorstCase.RegevSketch

theorem source_replacement_joint_hybrid {Ω α : Type*} [Fintype Ω] [Fintype α]
    (actualPool referencePool : Ω → ℝ)
    (_hp : ∀ sample, 0 ≤ actualPool sample) (hq : ∀ sample, 0 ≤ referencePool sample)
    (hpmass : ∑ sample, actualPool sample = 1)
    (hqmass : ∑ sample, referencePool sample = 1)
    (sourceError : ℝ)
    (hsource : (∑ sample, |actualPool sample-referencePool sample|) ≤ 2*sourceError)
    (actual : Ω → ℕ → EuclideanSpace ℂ α →ₗᵢ[ℂ] EuclideanSpace ℂ α)
    (ideal : ℕ → EuclideanSpace ℂ α →ₗᵢ[ℂ] EuclideanSpace ℂ α)
    (count : ℕ) (state : EuclideanSpace ℂ α) (hstate : ‖state‖ = 1)
    (event : α → Prop) (failure : ℕ → ℝ)
    (hstep : ∀ index<count,
      (∑ sample,referencePool sample*
        ‖actual sample index (evolve ideal index state)-ideal index (evolve ideal index state)‖^2) ≤
          2*failure index) :
    |(∑ sample, actualPool sample * bornEvent event (evolve (actual sample) count state)) -
      bornEvent event (evolve ideal count state)| ≤
      sourceError + ∑ index ∈ Finset.range count, 4*Real.sqrt (failure index) := by sorry

end InfoLossLAR.WorstCase.RegevSketch
