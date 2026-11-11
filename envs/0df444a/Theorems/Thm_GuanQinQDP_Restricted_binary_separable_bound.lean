-- Prove2me | Theorems.Thm_GuanQinQDP_Restricted_binary_separable_bound
-- name    : GuanQinQDP.Restricted.binary_separable_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:42:49.353667+00:00
-- url     : https://prove2.me/theorems/d8999728-53ec-4e34-a98f-3d76bd01bc5a
-- title:
--   Lemma 4.2 — binary separable-event bound by the standalone profile
-- statement:
--   Let $E:L(H_A)\to M_2$ be a channel with arbitrary finite-dimensional input and qubit output. Let $R$ be a finite-dimensional space and $\gamma\ge1$. Suppose $K$ is an effect on $\mathbb C^2\otimes R$ such that both $K$ and $I-K$ are separable across $\mathbb C^2:R$. Then for all $\rho,\sigma\in D(H_A\otimes R)$ with $\operatorname{Tr}_A\rho=\operatorname{Tr}_A\sigma$,
--
--   $$\operatorname{Tr}\big[K(E\otimes\mathrm{id}_R)(\rho-\gamma\sigma)\big]\le\Delta^{\mathrm{ALL}}_E(\gamma).$$
--
--   The input pairs need only equal marginals on $R$; they need not be neighbors. There is no multiplicative loss.
--
--   A separable effect is a sum of unnormalized product terms, so bounding it term by term would inflate the additive error. The lemma removes this loss for binary measurements whose complement is also separable. It is the step that converts PPT events into the standalone guarantee in Theorem 4.1.
--
--   Differences from the source:
--
--   - encoding: K and I − K separable → IsSeparablePositive K and IsSeparablePositive (1 − K): finite sums of nonnegative multiples of products of density operators; reason: the same as finite sums of products of positive semidefinite factors
--   - encoding: Tr[K(E ⊗ id_R)(ρ − γσ)] → real part of the trace; reason: the operator is Hermitian, so the trace is real
--   - encoding: Δ^ALL_E(γ) → standaloneProfile E γ: sSup over all ordered pairs of input density operators on H_A and all effects on M₂; reason: with one register every pair of states is neighboring (§2.1, replacement channel), so this is Definition 2.3 with n = 1; the set is nonempty and bounded by 1
-- source:
--   Ji Guan, Yecheng Qin, Parallel Composition of Quantum Differential Privacy: The Role of Measurement Restrictions, STOC 2027 submission #1640 (October 2026), source.pdf SHA-256 da23c8347251683a16df4c61de3fa1604211cdbf34d757a7a45feb0efd54c694, Lemma 4.2, eq. (12) (printed p. 18 / PDF p. 19)

import Definitions.Def_GuanQinQDP_Restricted_Model
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
open QAlgorithms WildeQIT.EntBreaking QAlgorithms.Entanglement

namespace GuanQinQDP.Restricted

/-- Lemma 4.2 (Binary separable-event bound), Guan–Qin, STOC 2027 submission #1640, printed
p. 18 / PDF p. 19. Let `E : L(H_A) → M₂` be a channel (any finite input dimension, qubit
output), `R` a finite-dimensional space and `γ ≥ 1`. If `K` is an effect on `ℂ² ⊗ R` such that
both `K` and `I − K` are separable across `ℂ² : R`, then for all `ρ, σ ∈ D(H_A ⊗ R)` with
`Tr_A ρ = Tr_A σ`,
`Tr[K (E ⊗ id_R)(ρ − γσ)] ≤ Δ^ALL_E(γ)`. -/
theorem binary_separable_bound {a R : Type} [Fintype a] [DecidableEq a] [Fintype R]
    [DecidableEq R] (E : Matrix a a ℂ →ₗ[ℂ] Matrix Qubit Qubit ℂ) (hE : IsQuantumChannel E)
    (γ : ℝ) (hγ : 1 ≤ γ) (K : Matrix (Qubit × R) (Qubit × R) ℂ) (hK : IsEffect K)
    (hKsep : IsSeparablePositive K) (hKcompl : IsSeparablePositive (1 - K))
    (ρ σ : Matrix (a × R) (a × R) ℂ) (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ)
    (hmarg : traceLeft ρ = traceLeft σ) :
    (K * applyFirst E (ρ - (γ : ℂ) • σ)).trace.re ≤ standaloneProfile E γ := by sorry

end GuanQinQDP.Restricted
