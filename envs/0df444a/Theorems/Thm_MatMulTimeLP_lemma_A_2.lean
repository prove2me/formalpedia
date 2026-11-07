-- Prove2me | Theorems.Thm_MatMulTimeLP_lemma_A_2
-- name    : MatMulTimeLP.lemma_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:51:48.377033+00:00
-- url     : https://prove2.me/theorems/e2881387-2c89-4a39-b831-1d395cfd29c6
-- title:
--   Lemma A.2 — fixed residuals are accurate with probability $1-n^{-14}$; the walk is within a factor $2$
-- statement:
--   Let $n=2^D$, $D\ge 1$, with $n\ge k$. For every fixed residual $r$, chosen independently of $G$, the probability that $r$ is not accurate for $G$ is at most $n^{-14}$. Moreover, if $r$ is accurate for $G$, then $E\le\tilde E\le 2E$, where $E=\|r\|_2^2$, and if additionally $E>0$, then
--
--   $$\frac{r_i^2}{2E}\le\pi_i\le\frac{2r_i^2}{E}\quad\text{for every }i\in[n].$$
--
--   This justifies using the sketch only as a proposal: its estimates are correct up to a factor of two, which the rejection step of Sample then cancels.
--
--   Differences from the source:
--   - encoding: "we assume that $n$ is a power of two" and $n\ge k$ (p.44); $\alpha=1/(8D)$ → $n=2^D$, `skK D ≤ 2 ^ D`, `1 ≤ D`; reason: the appendix's own setting; $D=0$ would make $\alpha$ undefined
--   - encoding: the probability over $G\in\mathbb R^{k\times n}$ → the product Gaussian law on `Fin k × Fin n → ℝ`; reason: same law; Lean's product measure needs a function type
-- source:
--   Jiang–Kyng–Zöcklein, Solving Linear Programs in Truly Matrix Multiplication Time, STOC 2027 submission (manuscript sha256 6539350a…81ffcc), Lemma A.2, p.45; parameters p.44

import Mathlib
import Definitions.Def_MatMulTimeLP_Sampler

namespace MatMulTimeLP

/-- Jiang–Kyng–Zöcklein, *Solving Linear Programs in Truly Matrix Multiplication Time*, STOC 2027
submission (manuscript sha256 6539350a…81ffcc), Lemma A.2, p.45: a residual fixed independently of `G` is not
accurate with probability at most `n⁻¹⁴`; and if `r` is accurate for `G` then `E ≤ Ẽ ≤ 2E`, and if also `E > 0` then
`rᵢ²/(2E) ≤ πᵢ ≤ 2rᵢ²/E` for every `i`.

**Formalization Note** `n = 2^D`, `n ≥ k` as Appendix A assumes (p.44), and `D ≥ 1` so that `α = 1/(8D)` has its
meaning. The first bound is on the sketch law, for fixed `r`. -/
theorem lemma_A_2 (D : ℕ) (hD : 1 ≤ D) (hk : skK D ≤ 2 ^ D) (r : Fin (2 ^ D) → ℝ) :
    sketchLaw (skK D) (2 ^ D) {G | ¬ Accurate D G r} ≤ ENNReal.ofReal (1 / ((2 : ℝ) ^ D) ^ 14) ∧
    ∀ G : Fin (skK D) × Fin (2 ^ D) → ℝ, Accurate D G r →
      energyE r ≤ estE D G r ∧ estE D G r ≤ 2 * energyE r ∧
      (0 < energyE r → ∀ i, r i ^ 2 / (2 * energyE r) ≤ proposal D G r i ∧
        proposal D G r i ≤ 2 * r i ^ 2 / energyE r) := by sorry

end MatMulTimeLP
