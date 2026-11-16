-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_adaptive_stages_l1
-- name    : InfoLossLAR.WorstCase.RegevSketch.adaptive_stages_l1
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T09:26:18.924707+00:00
-- url     : https://prove2.me/theorems/d8ca124d-12da-47d6-adec-74b5945fefa0
-- title:
--   Joint L1 error propagation for adaptive finite-state stages
-- statement:
--   Let $P_i,Q_i$ be probability laws on the same finite state space. Suppose $P_{i+1}$ and $Q_{i+1}$ are obtained by applying respective stochastic kernels $K_i$ and $L_i$. Assume the initial $L^1$ distance is at most $\delta$ and that for every state $x$ the two conditional output laws at step $i$ have $L^1$ distance at most $e_i$. Then
--
--   $$
--   \|P_n-Q_n\|_1\le\delta+\sum_{i=0}^{n-1}e_i.
--   $$
--
--   The state may retain the complete common random pool and every previous transcript, so the kernels may depend on that retained history. The theorem assumes a uniform conditional bound for each state; it does not derive that bound from an average error or assume that reuse of a pool gives independent steps. It is an error-accounting interface for classical stages in the DGS reduction and does not construct a quantum circuit.
--
--   **Formalization Note.** The laws are `AFT.FiniteDist`; $L^1$ is the sum of absolute differences of weights, without the factor $1/2$ used in total variation.
-- source:
--   Oded Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, https://cims.nyu.edu/~regev/papers/qcrypto.pdf, Theorem 3.1 and Lemma 3.3, pp. 18–19. This elementary adaptive finite-channel error-propagation lemma is a separately formalized aid, not a verbatim theorem or a claim that the DGS iteration has been implemented.

import Definitions.Def_InfoLossLAR_LoadedBatchBundle_05
set_option autoImplicit false
open AFT
open scoped BigOperators

theorem InfoLossLAR.WorstCase.RegevSketch.adaptive_stages_l1 {State : Type*} [Fintype State]
    (actual ideal : ℕ → FiniteDist State)
    (actualStep idealStep : ℕ → State → FiniteDist State)
    (δ : ℝ) (error : ℕ → ℝ)
    (hstart : (∑ x, |(actual 0).weight x-(ideal 0).weight x|) ≤ δ)
    (hactual : ∀ i, actual (i+1) = (actual i).mix (actualStep i))
    (hideal : ∀ i, ideal (i+1) = (ideal i).mix (idealStep i))
    (hstep : ∀ i state, (∑ x, |(actualStep i state).weight x-(idealStep i state).weight x|) ≤ error i) :
    ∀ n, (∑ x, |(actual n).weight x-(ideal n).weight x|) ≤ δ + ∑ i ∈ Finset.range n, error i := by sorry
