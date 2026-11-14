-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_coherent_decoder_copy_error
-- name    : InfoLossLAR.WorstCase.coherent_decoder_copy_error
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-13T22:46:19.793013+00:00
-- url     : https://prove2.me/theorems/15a4a871-d31a-4baf-acf2-46cba2992f4b
-- title:
--   Coherent copying and uncomputation: exact error identity and square-root failure bound
-- statement:
--   Let $A$ and $B$ be finite sets, let $\psi:A\to\mathbb C$ be an arbitrary amplitude vector, and let $r,d:A\to B$ be the computed and desired classical answers. The register indexed by $A$ retains all workspace and any query label. Copy the answer into a fresh register, obtaining
--   $$|v_r\rangle=\sum_{a\in A}\psi(a)|a,r(a)\rangle,\qquad |v_d\rangle=\sum_{a\in A}\psi(a)|a,d(a)\rangle.$$
--   For any complex-linear isometry $U$ into a seminormed complex vector space, if the failure mass $p=\sum_{a:r(a)\ne d(a)}|\psi(a)|^2$ satisfies $p\le\varepsilon$, then
--   $$\|U v_r-U v_d\|^2=2p,\qquad\|U v_r-U v_d\|\le2\sqrt\varepsilon.$$
--   Normalization is unnecessary for the identity; for a normalized decoder state, $p$ is precisely its classical failure probability. Taking $U$ to be uncomputation establishes the semantic error estimate needed in the coherent-decoder step of the Gaussian LWE worst-case reduction. The statement does not assert an efficient implementation of $U$ or construct the Regev reduction.
-- source:
--   Auxiliary formalization of the coherent compute-copy-uncompute estimate used in Chen Qian, Information Loss Is All You Need, arXiv:2611.05136v1, Appendix I.1, pp. 132–133. https://arxiv.org/html/2611.05136v1

import Mathlib

set_option autoImplicit false

theorem InfoLossLAR.WorstCase.coherent_decoder_copy_error
    {α β E : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    (U : EuclideanSpace ℂ (α × β) →ₗᵢ[ℂ] E)
    (ψ : α → ℂ) (readout desired : α → β) (ε : ℝ)
    (hfailure : (∑ x : α, if readout x = desired x then 0 else ‖ψ x‖ ^ 2) ≤ ε) :
    let actual : EuclideanSpace ℂ (α × β) :=
      WithLp.toLp 2 (fun p => if p.2 = readout p.1 then ψ p.1 else 0)
    let ideal : EuclideanSpace ℂ (α × β) :=
      WithLp.toLp 2 (fun p => if p.2 = desired p.1 then ψ p.1 else 0)
    ‖U actual - U ideal‖ ^ 2 =
      (2 * ∑ x : α, if readout x = desired x then 0 else ‖ψ x‖ ^ 2) ∧
    ‖U actual - U ideal‖ ≤ 2 * Real.sqrt ε := by sorry
