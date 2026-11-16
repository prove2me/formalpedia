-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_decoder_failure_to_joint_event
-- name    : InfoLossLAR.WorstCase.RegevSketch.decoder_failure_to_joint_event
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T10:21:40.279845+00:00
-- url     : https://prove2.me/theorems/04dcee54-01a2-4023-a702-418a9bf291ce
-- title:
--   Coherent decoder query failures bound a complete joint output event
-- statement:
--   Let $P$ and $Q$ be probability distributions on a finite set of complete sample pools, with total variation at most $\delta$. Consider a normalized initial state, ideal isometries independent of the pool, and actual isometries that may reuse the same pool at every step. Suppose that at every ideal prefix the actual and ideal step outputs have the following common compute/copy/uncompute representation: both start from the same decoder workspace amplitudes and use the same pool-dependent uncomputation isometry, while one copies the decoder's actual answer and the other copies the correct answer. The ideal query amplitudes are normalized and do not depend on the pool.
--
--   If, at step $i$ for each query, the decoder's workspace-weighted failure probability averaged over $Q$ is at most $\varepsilon_i$, then every event $F$ on the complete final measured register satisfies
--
--   $$
--   \left|\mathbb E_{P}\Pr_{\mathrm{actual},\omega}[F]-\Pr_{\mathrm{ideal}}[F]\right|
--   \le \delta + 4\sum_{i=0}^{m-1}\sqrt{\varepsilon_i}.
--   $$
--
--   The common uncomputation and exact ideal-prefix representation are explicit assumptions, not assertions that a BDD or DGS circuit has been constructed. Pool replacement is charged once, and no independence is assumed between steps.
--
--   **Formalization Note.** The decoder's workspace and copied answer register are retained as finite complex Euclidean spaces. The pool-distance hypothesis uses half the $L^1$ distance of its weights.
-- source:
--   Oded Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, https://cims.nyu.edu/~regev/papers/qcrypto.pdf, Lemmas 3.3 and 3.14, pp. 18–19 and 26–27. This is a conditional finite-dimensional compute/copy/uncompute error estimate, not the construction in those lemmas.

import Definitions.Def_RegevJointHybrid
set_option autoImplicit false
open scoped BigOperators
open RegevJointHybrid

namespace InfoLossLAR.WorstCase.RegevSketch

theorem decoder_failure_to_joint_event
    {Ω ι W β α : Type*} [Fintype Ω] [Fintype ι] [Fintype W]
    [Fintype β] [Fintype α] [DecidableEq β]
    (actualPool referencePool : Ω → ℝ)
    (hp : ∀ sample, 0 ≤ actualPool sample) (hq : ∀ sample, 0 ≤ referencePool sample)
    (hpmass : ∑ sample, actualPool sample = 1)
    (hqmass : ∑ sample, referencePool sample = 1)
    (sourceError : ℝ)
    (hsource : (∑ sample, |actualPool sample-referencePool sample|) ≤ 2*sourceError)
    (actual : Ω → ℕ → EuclideanSpace ℂ α →ₗᵢ[ℂ] EuclideanSpace ℂ α)
    (ideal : ℕ → EuclideanSpace ℂ α →ₗᵢ[ℂ] EuclideanSpace ℂ α)
    (count : ℕ) (state : EuclideanSpace ℂ α) (hstate : ‖state‖ = 1)
    (event : α → Prop) (failure : ℕ → ℝ)
    (amplitude : ℕ → ι → ℂ) (work : Ω → ℕ → ι → W → ℂ)
    (readout : Ω → ℕ → ι → W → β) (answer : ℕ → ι → β)
    (uncompute : Ω → ℕ → EuclideanSpace ℂ ((ι × W) × β) →ₗᵢ[ℂ] EuclideanSpace ℂ α)
    (hamplitude : ∀ index < count, ∑ query, ‖amplitude index query‖^2 = 1)
    (hfailure : ∀ index < count, ∀ query,
      (∑ pool, referencePool pool *
        ∑ workState, if readout pool index query workState = answer index query
          then 0 else ‖work pool index query workState‖^2) ≤ failure index)
    (hactual : ∀ pool index, index < count →
      actual pool index (evolve ideal index state) =
        uncompute pool index (WithLp.toLp 2 (fun p : (ι × W) × β =>
          if p.2 = readout pool index p.1.1 p.1.2 then
            amplitude index p.1.1 * work pool index p.1.1 p.1.2 else 0)))
    (hideal : ∀ pool index, index < count →
      ideal index (evolve ideal index state) =
        uncompute pool index (WithLp.toLp 2 (fun p : (ι × W) × β =>
          if p.2 = answer index p.1.1 then
            amplitude index p.1.1 * work pool index p.1.1 p.1.2 else 0))) :
    |(∑ sample, actualPool sample * bornEvent event (evolve (actual sample) count state)) -
      bornEvent event (evolve ideal count state)| ≤
      sourceError + ∑ index ∈ Finset.range count, 4*Real.sqrt (failure index) := by sorry

end InfoLossLAR.WorstCase.RegevSketch
