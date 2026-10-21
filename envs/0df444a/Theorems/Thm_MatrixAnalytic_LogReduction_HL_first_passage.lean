-- Prove2me | Theorems.Thm_MatrixAnalytic_LogReduction_HL_first_passage
-- name    : MatrixAnalytic.LogReduction.HL_first_passage
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:46:12.342452+00:00
-- url     : https://prove2.me/theorems/249dc235-9231-4a2e-a369-bba6f064cf8b
-- title:
--   Eqs. (8.45)–(8.46) — H^[k] and L^[k] are the first passage probabilities from ℓ(2^k) to ℓ(2^{k+1}) and ℓ(0)
-- statement:
--   Let $\{X_t\}$ be an irreducible homogeneous QBD with transition matrix (8.1), and let $H^{[k]}, L^{[k]}, U^{[k]}$ be the matrices of the logarithmic reduction recursion
--   $$H^{[0]}=(I-A_1)^{-1}A_0,\quad L^{[0]}=(I-A_1)^{-1}A_2,\quad H^{[k+1]}=(I-U^{[k]})^{-1}(H^{[k]})^2,\quad L^{[k+1]}=(I-U^{[k]})^{-1}(L^{[k]})^2,\quad U^{[k]}=H^{[k]}L^{[k]}+L^{[k]}H^{[k]},$$
--   where $(I-M)^{-1}$ denotes $\sum_{\nu\ge0}M^\nu$. Then every entry of $\sum_\nu A_1^\nu$ is finite, and for every $k\ge0$:
--   $$H^{[k]}=\mathrm P[\delta(k+1)<\gamma(0)\ \&\ X_{\delta(k+1)}\mid X_0\in\ell(2^k)],\qquad L^{[k]}=\mathrm P[\gamma(0)<\delta(k+1)\ \&\ X_{\gamma(0)}\mid X_0\in\ell(2^k)],$$
--   the row sums of $U^{[k]}$ are at most $1$, and every entry of $\sum_\nu(U^{[k]})^\nu$ is finite. Here $\gamma(0)$ is the first passage time to $\ell(0)$ and $\delta(k+1)$ that to $\ell(2^{k+1})$; $H^{[k]}_{ij}$ is the probability, starting from $(2^k,i)$, of reaching $\ell(2^{k+1})$ before $\ell(0)$ and doing so in phase $j$, and $L^{[k]}_{ij}$ that of reaching $\ell(0)$ before $\ell(2^{k+1})$, in phase $j$.
--
--   These two identities are the first step of the proof of Theorem 8.4.1: they give the matrices of the recursion their probabilistic meaning, and the finiteness statements say that the inverses $(I-U^{[k]})^{-1}$ of the recursion are genuine (the book: "$U^{[k]}$ is substochastic and $(I-U^{[k]})$ is nonsingular").
--
--   **Formalization Note** Inverses are the series $\sum_\nu M^\nu$ computed entrywise in $[0,\infty]$ (the book's convention, p. 109); their finiteness is part of the conclusion, not a hypothesis. Probabilities are sums over finite trajectories, and the number of phases may be infinite.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 191, Eqs. (8.45)–(8.46), and p. 192 (U^[k] substochastic, I − U^[k] nonsingular)

import Mathlib
import Definitions.Def_MatrixAnalytic_LogReduction_Chain
import Definitions.Def_MatrixAnalytic_LogReduction_QBD
import Definitions.Def_MatrixAnalytic_LogReduction_Passage

open scoped ENNReal

namespace MatrixAnalytic.LogReduction

/-- Eqs. (8.45)–(8.46), p. 191, with the step "`U^{[k]}` is substochastic and `(I − U^{[k]})` is
nonsingular" of p. 192. For an irreducible QBD (8.1) and every `k ≥ 0`, the matrices `H^{[k]}`
and `L^{[k]}` of the recursion (8.40)–(8.44), with `(I − M)⁻¹ := Σ_{ν≥0} M^ν`, are the
probabilities, starting from `ℓ(2^k)`, of reaching `ℓ(2^{k+1})` before `ℓ(0)` (8.45) and `ℓ(0)`
before `ℓ(2^{k+1})` (8.46), recorded with the phase at that epoch; `U^{[k]}` (8.44) has row sums
at most `1`; and every entry of `Σ_ν (U^{[k]})^ν` and of `Σ_ν A₁^ν` is finite. -/
theorem HL_first_passage {ι : Type*} [Countable ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂)) :
    (∀ i j : ι, seriesInvE (ennMat A₁) i j ≠ ⊤) ∧
    ∀ k : ℕ,
      logH A₀ A₁ A₂ k = hitUp (qbdP B A₀ A₁ A₂) k ∧
      logL A₀ A₁ A₂ k = hitDown (qbdP B A₀ A₁ A₂) k ∧
      (∀ i : ι, ∑' j : ι, logU A₀ A₁ A₂ k i j ≤ 1) ∧
      ∀ i j : ι, seriesInvE (logU A₀ A₁ A₂ k) i j ≠ ⊤ := by sorry

end MatrixAnalytic.LogReduction
