-- Prove2me | Theorems.Thm_LiqPremiaEq_lemma_7_1
-- name    : LiqPremiaEq.lemma_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:02:27.10355+00:00
-- url     : https://prove2.me/theorems/c9ef5824-5877-421c-a437-5592ff45ead5
-- title:
--   Lemma 7.1 — $\Gamma$ is positive definite and has only positive eigenvalues
-- statement:
--   Let $N\ge2$, $\gamma^1,\dots,\gamma^N>0$ with $\gamma^N=\max\{\gamma^1,\dots,\gamma^N\}$, and let $\Gamma$ be the risk-aversion matrix (4.7). Then
--
--   1. $\Gamma$ is positive definite: $b^\top\Gamma b>0$ for every $b\in\mathbb R^{N-1}\setminus\{0\}$;
--   2. every (complex) eigenvalue of $\Gamma$ is real and positive.
--
--   $\Gamma$ is in general not symmetric, so neither part implies the other (footnote 19). Positive definiteness of $\Gamma$ enters the proof that the Riccati solution $F$ stays positive semidefinite (Corollary 7.7).
--
--   Differences from the source:
--   - reading: positive (semi)definite → IsPSDQuad A: bᵀAb ≥ 0 for all b (IsPDQuad: bᵀAb > 0 for b ≠ 0), no symmetry required; reason: footnotes 10 (p.8) and 19 (p.14): the matrices are not symmetric and the notions are meant without symmetry
--   - reading: “has only positive eigenvalues” → every element z of the complex spectrum of Γ satisfies Im z = 0 and Re z > 0; reason: footnote 19 separates this from positive definiteness, which for a non-symmetric matrix gives only positive real parts; the paper cites it from [21, Lemma A.5]
--   - encoding: agents n = 1, …, N with N ≥ 2; agent N the most risk-averse (3.2) → agents Fin (M + 1) with 1 ≤ M; agent N is Fin.last M; agents 1, …, N − 1 are Fin M via Fin.castSucc; reason: a relabelling of the same agents
-- source:
--   Muhle-Karbe–Shi–Yang, An Equilibrium Model for the Cross-Section of Liquidity Premia, arXiv:2011.13625v1, Lemma 7.1, p.14 (with (3.2), p.4, and footnote 19)

import Mathlib
import Definitions.Def_LiqPremiaEq_Gam
import Definitions.Def_LiqPremiaEq_IsPSDQuad

open Matrix

namespace LiqPremiaEq

/-- **Lemma 7.1.** The risk-aversion matrix `Γ` of (4.7) is positive definite (`bᵀΓb > 0` for
`b ≠ 0`, without symmetry) and has only positive eigenvalues: every complex eigenvalue of `Γ`
is real and positive.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, Lemma 7.1, p.14 (with (3.2), p.4, and footnote 19).

**Formalization Note** `N = M + 1 ≥ 2` agents, `γⁿ > 0`, agent `N = Fin.last M` the most
risk-averse (3.2). Eigenvalues are the spectrum of `Γ` as a complex matrix. -/
theorem lemma_7_1 {M : ℕ} (hM : 1 ≤ M) (γ : Fin (M + 1) → ℝ) (hγ : ∀ n, 0 < γ n)
    (hγN : ∀ n, γ n ≤ γ (Fin.last M)) :
    IsPDQuad (Gam γ) ∧
      ∀ z ∈ spectrum ℂ ((Gam γ).map (algebraMap ℝ ℂ)), z.im = 0 ∧ 0 < z.re := by sorry

end LiqPremiaEq
