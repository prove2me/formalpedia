-- Prove2me | Theorems.Thm_FourierRankQLB_lemma_3_2
-- name    : FourierRankQLB.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:43:54.994537+00:00
-- url     : https://prove2.me/theorems/c88879c8-2bd9-46dd-aed8-08ac76cadb9d
-- title:
--   Lemma 3.2 — controlled rank-one phase growth
-- statement:
--   Let $(Y,\nu)$ be a $\sigma$-finite measure space, $K$ a separable Hilbert space, and $\Gamma:Y\to\mathbb R^{n\times n}$ measurable with $\operatorname{rank}\Gamma(y)\le1$ for almost every $y$. Define
--   $$
--   (P_\Gamma\Psi)(Q,y)=\chi_{\Gamma(y)}(Q)\,\Psi(Q,y).
--   $$
--   Then $P_\Gamma$ is unitary, and
--   $$
--   P_\Gamma W_r(Y,K)\subseteq W_{r+1}(Y,K)
--   $$
--   for every $r\ge0$. The same statement holds for $P_\Gamma^{-1}$.
--
--   This is the basic example of a query of Fourier-rank cost one.
--
--   Differences from the source:
--
--   - encoding: $\Gamma:Y\to\mathbb R^{n\times n}$ measurable → every entry of $\Gamma$ measurable; reason: the matrices carry no default σ-algebra in Lean; entrywise measurability is the Borel measurability of a finite-dimensional map
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Lemma 3.2, p.17

import Mathlib
import Definitions.Def_FourierRankQLB_Wr

open MeasureTheory

namespace FourierRankQLB

/-- Lemma 3.2 (Controlled rank-one phase growth). For a measurable `Γ : Y → ℝ^{n×n}` with
`rank Γ(y) ≤ 1` almost everywhere, the operator `(P_Γ Ψ)(Q, y) = χ_{Γ(y)}(Q) Ψ(Q, y)` of Eq. (21) is
unitary, and both `P_Γ` and `P_Γ⁻¹` map `W_r(Y, K)` into `W_{r+1}(Y, K)` for every `r`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Lemma 3.2, p. 17.

**Formalization Note.** `(Y, ν)` is σ-finite and `K` a separable Hilbert space, the setting of Eq. (20).
Measurability of `Γ` is entrywise. The operator is an isometric equivalence of
`L²(O(n) × Y, μ_n ⊗ ν; K)` given by the formula (21). -/
theorem lemma_3_2 {n : ℕ} {Y : Type} [MeasurableSpace Y] (ν : Measure Y) [SigmaFinite ν]
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [TopologicalSpace.SeparableSpace K] (Γ : Y → Matrix (Fin n) (Fin n) ℝ)
    (hΓ : ∀ i j, Measurable fun y => Γ y i j) (hrank : ∀ᵐ y ∂ν, (Γ y).rank ≤ 1) :
    ∃ P : Lp K 2 ((haarO n).prod ν) ≃ₗᵢ[ℂ] Lp K 2 ((haarO n).prod ν),
      (∀ Ψ, P Ψ =ᵐ[(haarO n).prod ν] fun p => chi (Γ p.2) p.1 • Ψ p) ∧
      (∀ r, ∀ Ψ ∈ Wr n r ν K, P Ψ ∈ Wr n (r + 1) ν K) ∧
      (∀ r, ∀ Ψ ∈ Wr n r ν K, P.symm Ψ ∈ Wr n (r + 1) ν K) := by sorry

end FourierRankQLB
