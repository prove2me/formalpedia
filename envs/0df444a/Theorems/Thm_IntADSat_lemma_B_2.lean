-- Prove2me | Theorems.Thm_IntADSat_lemma_B_2
-- name    : IntADSat.lemma_B_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:51:37.984109+00:00
-- url     : https://prove2.me/theorems/100d5149-c35d-4fd4-87f5-bc0102c68803
-- title:
--   Lemma B.2 — random $0/1$ matrices are integer surjective
-- statement:
--   Let $B$ be a $k\times m$ matrix with independent uniform $\{0,1\}$ entries, where $k\ge1$ and $m\ge16k$, and put $h=\lfloor m/2\rfloor$. Then
--
--   $$
--   \Pr\big[B\mathbb Z^m\neq\mathbb Z^k\big]\le\Big(1+\frac k2\log_2\max(2,k)\Big)\exp(-h/16).
--   $$
--
--   This is the probabilistic input of the integer construction: rectangular adjacency blocks with many more columns than rows are integer surjective.
--
--   Differences from the source:
--   - encoding: matrix with independent uniform {0,1} entries → uniform count over patterns b : Fin k → Fin m → Bool divided by 2^(km); reason: same law
--   - encoding: h = ⌊m/2⌋ → natural-number division m / 2; reason: same value
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Lemma B.2, p.15 (PDF 16)

import Mathlib
import Definitions.Def_IntADSat_probMat

set_option autoImplicit false

namespace IntADSat

/-- **Lemma B.2** (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), p.15 (PDF 16)). Let `B` be a `k × m` matrix with independent uniform `{0, 1}`
entries, where `k ≥ 1` and `m ≥ 16k`, and put `h = ⌊m/2⌋`. Then
`Pr[Bℤᵐ ≠ ℤᵏ] ≤ (1 + (k/2) log₂ max(2, k)) exp(−h/16)`. -/
theorem lemma_B_2 (k m : ℕ) (hk : 1 ≤ k) (hm : 16 * k ≤ m) :
    probMat k m (fun b => ¬ ∀ y : Fin k → ℤ, ∃ x : Fin m → ℤ,
        (Matrix.of fun i j => if b i j then (1 : ℤ) else 0).mulVec x = y) ≤
      (1 + (k : ℝ) / 2 * Real.logb 2 (max 2 (k : ℝ))) * Real.exp (-((m / 2 : ℕ) : ℝ) / 16) := by sorry

end IntADSat
