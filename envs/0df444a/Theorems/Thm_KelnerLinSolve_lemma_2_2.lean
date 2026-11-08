-- Prove2me | Theorems.Thm_KelnerLinSolve_lemma_2_2
-- name    : KelnerLinSolve.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:55:19.62166+00:00
-- url     : https://prove2.me/theorems/b07418b4-01b1-4503-8c04-a4a6b6fcab5e
-- title:
--   Lemma 2.2 — the residuals of Dixon's lifting satisfy $\|b_j\|_\infty \le \max(\|b\|_\infty, \|M\|_\infty)$
-- statement:
--   Let $R\ge2$ and let $M, C\in\mathbb Z^{n\times n}$ satisfy $MC\equiv I\pmod R$. For $b\in\mathbb Z^n$, every residual $b_j$ of Dixon's lifting (the recurrence (2)–(3)) satisfies
--
--   $$
--   \|b_j\|_\infty \le W := \max\big(\|b\|_\infty, \|M\|_\infty\big),
--   $$
--
--   where $\|b\|_\infty = \max_i |b_i|$ and $\|M\|_\infty = \max_i\sum_j|M_{ij}|$ is the maximum absolute row sum.
--
--   The bound keeps every intermediate number of the lifting at $O(\log W)$ bits.
--
--   Differences from the source:
--   - generalization: C from Step 1 has entries in {0, …, R − 1} → any integer matrix C with MC ≡ I (mod R); reason: the argument never uses the range of C; specializes to Step 1's C
--   - encoding: M invertible with gcd(R, det M) = 1 → not stated as hypotheses; reason: implied by MC ≡ I (mod R), R ≥ 2
--   - encoding: ∥·∥_∞ of vectors and of matrices (row sums) → `supNormZ` and `rowSumNorm`, natural numbers; reason: same values
-- source:
--   Kelner, Solving Linear Systems in Õ(mn log(κ/ε)) Bit Operations, STOC 2027 submission (sha256 d1af55cb…), Lemma 2.2, p.6 (row-sum norm defined before it, p.6)

import Mathlib
import Definitions.Def_KelnerLinSolve_dixonRes

open Matrix

namespace KelnerLinSolve

/-- **Lemma 2.2**, Kelner, *Solving Linear Systems in Õ(mn log(κ/ε)) Bit Operations*, STOC 2027
submission (sha256 d1af55cb…), p.6. "The residual vectors computed during Step 2 of Dixon's algorithm
have `‖b_j‖_∞ ≤ W := max(‖b‖_∞, ‖M‖_∞)`", where "`‖M‖_∞ = maxᵢ ∑ⱼ |M_{ij}|` is the maximum absolute
row sum".

In the setting of §2.1 (integers `R ≥ 2`, integer matrices `M, C` with `M C ≡ I (mod R)`), every
residual `b_j` of the recurrence (2)–(3) satisfies the bound, for every `j`.

**Formalization Note.** `‖b‖_∞` is `supNormZ` (largest absolute coordinate) and `‖M‖_∞` is
`rowSumNorm` (largest absolute row sum), both natural numbers. The entries of `C` are not required
to lie in `{0, …, R − 1}`. -/
theorem lemma_2_2 {n : ℕ} (M C : Matrix (Fin n) (Fin n) ℤ) (R : ℤ) (b : Fin n → ℤ)
    (hR : 2 ≤ R) (hMC : ∀ i j, R ∣ (M * C - 1) i j) :
    ∀ j : ℕ, supNormZ (dixonRes M C R b j) ≤ max (supNormZ b) (rowSumNorm M) := by sorry

end KelnerLinSolve
