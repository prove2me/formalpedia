-- Prove2me | Theorems.Thm_L22EigEst_claim_3_2
-- name    : L22EigEst.claim_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:23:16.535301+00:00
-- url     : https://prove2.me/theorems/b7bb6a1d-d0cf-4406-9672-f0d51eaf7348
-- title:
--   Claim 3.2 — $VAV^\top$ has row norms $\|A_i\|_2^2/s$ and bounded row norms
-- statement:
--   Let $A\in\mathbb R^{n\times n}$ be symmetric, $s\ge1$ an integer, and $V\in\mathbb R^{sn\times n}$ the matrix of Algorithm 2 ($s$ stacked copies of $I_n$, rescaled by $1/\sqrt s$). Then for every row $l$ of $VAV^\top$, with $i\equiv l\pmod n$,
--
--   $$\|(VAV^\top)_l\|_2^2=\frac{\|A_i\|_2^2}{s}\qquad\text{and}\qquad \frac{s\,\|(VAV^\top)_l\|_2^2}{\|VAV^\top\|_F^2}\le1 .$$
--
--   So $VAV^\top$ satisfies the bounded row-norm property (1) with the same $s$, and its row norms are computable from those of $A$. This lets Algorithm 2 run Algorithm 1 on $VAV^\top$ for an arbitrary symmetric $A$.
--
--   Differences from the source:
--   - generalization: s = ⌈c log(1/ε)/ε²⌉ for ε ∈ (0, 1) → any integer s ≥ 1 (no ε); reason: the claim and its proof use only that s is a positive integer; the paper's s is ≥ 1 for c > 0
--   - encoding: row l ∈ [sn] with i ≡ l (mod n) → row l = (k, i) ∈ Fin s × Fin n; reason: Lean indexing of the stacked copies; same rows
--   - encoding: s‖(VAV⊺)_l‖₂²/‖VAV⊺‖_F² ≤ 1 → s‖(VAV⊺)_l‖₂² ≤ ‖VAV⊺‖_F²; reason: multiplied out; equivalent for A ≠ 0, where the quotient is defined
-- source:
--   Menand, Waingarten, Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation, STOC 2027 submission (manuscript sha256 b1f6adce…), Claim 3.2, p.11

import Definitions.Def_L22EigEst_rowSq
import Definitions.Def_L22EigEst_stackV

open Matrix

namespace L22EigEst

/-- **Claim 3.2** (p.11), Menand, Waingarten, *Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation*, STOC 2027
submission (manuscript sha256 b1f6adce…): "Given a symmetric matrix A ∈ ℝ^{n×n} and accuracy parameter ε ∈ (0, 1), the matrix
VAV⊺ ∈ ℝ^{sn×sn} defined by Algorithm 2 satisfies ∀l ∈ [sn], ∥(VAV⊺)_l∥2² = ∥A_i∥2²/s and
s · ∥(VAV⊺)_l∥2²/∥VAV⊺∥F² ≤ 1, where i ≡ l (mod n) and s = ⌈c log(1/ε)/ε²⌉ is as in Algorithm 2."

**Formalization Note.** Stated for every integer `s ≥ 1` (the claim uses only that `s` is a
positive integer; `s = ⌈c log(1/ε)/ε²⌉ ≥ 1` for `c > 0`, `ε ∈ (0, 1)`). Row `l = (k, i)` of
`VAV⊺` (indexed by `Fin s × Fin n`) is the paper's row `l` with `i ≡ l (mod n)`. The second clause
is multiplied out (`s‖(VAV⊺)_l‖² ≤ ‖VAV⊺‖_F²`), equivalent for `A ≠ 0`. -/
theorem claim_3_2 (s n : ℕ) (hs : 1 ≤ s) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    ∀ l : Fin s × Fin n,
      rowSq (stackV s n * A * (stackV s n)ᵀ) l = rowSq A l.2 / s ∧
      (s : ℝ) * rowSq (stackV s n * A * (stackV s n)ᵀ) l ≤
        frobSq (stackV s n * A * (stackV s n)ᵀ) := by sorry

end L22EigEst
