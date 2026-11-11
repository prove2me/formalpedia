-- Prove2me | Theorems.Thm_LiuHelsenDesigns_OneD_theorem_2
-- name    : LiuHelsenDesigns.OneD.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T11:12:17.06881+00:00
-- url     : https://prove2.me/theorems/4be8b2e6-bd25-47dd-a26d-97cf83499e7f
-- title:
--   Theorem 2 — magic-augmented block designs
-- statement:
--   For every sufficiently large qubit count ξ, let ξ=mℓ with positive integers m and ℓ, and let $1\le k\le\xi-1$. Suppose $\ell\ge8\log_2k+2$ and each independent local block is a relative-error k-design with $0\le\varepsilon\le2^{-2\ell k}$. Sandwich an independent uniform ξ-qubit Clifford between two such product layers. The resulting law ν satisfies
--
--   $$
--   \nu\text{ is a }2^{k-\xi+4}\text{-relative-error }k\text{-design}.
--   $$
--
--   For every $0<\varepsilon'\le1$, if $\xi\ge k+\log_2(1/\varepsilon')+4$, the same law has relative error at most $\varepsilon'$. The statement retains every positive order, including orders one through four.
--
--   Differences from the source:
--   - reading: approximation errors and design order in the standing context → positive integer order and positive errors at most one (local exact blocks also allow zero); reason: the nontrivial precision regime of §2.1 and the surrounding construction
--   - encoding: the intermediate block construction with ℓ dividing ξ → positive block count m and ξ=mℓ; the final precision corollary uses a monotone inequality; reason: this is the temporary convention of p.3 and Eq.(54), never a hypothesis of Theorem 1
-- source:
--   Guoding Liu, Jonas Helsen, STOC 2027 submission #221 (October 2026), p. 5, Theorem 2. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/221.pdf

import Definitions.Def_LiuHelsenDesigns_OneD_blocks

namespace LiuHelsenDesigns.OneD
theorem theorem_2 : ∃ N : ℕ, ∀ ξ : ℕ, N ≤ ξ → ∀ ℓ m k : ℕ,
    1 ≤ ℓ → 1 ≤ m → ξ = m*ℓ → 1 ≤ k → k+1 ≤ ξ →
    8*Real.logb 2 k+2 ≤ ℓ → ∀ ε : ℝ, 0 ≤ ε → ε ≤ (2 : ℝ)^(-(2*ℓ*k : ℤ)) →
    ∀ ν₁ ν₂ : Fin m → MeasureTheory.Measure (Mat ℓ),
      (∀ i, RelativeDesign (ν₁ i) k ε) → (∀ i, RelativeDesign (ν₂ i) k ε) →
      RelativeDesign (magicLaw ξ ℓ m ν₁ ν₂) k ((2 : ℝ)^((k : ℤ)-ξ+4)) ∧
      ∀ ε' : ℝ, 0 < ε' → ε' ≤ 1 → (k : ℝ)+Real.logb 2 (1/ε')+4 ≤ ξ →
        RelativeDesign (magicLaw ξ ℓ m ν₁ ν₂) k ε' := by sorry
end LiuHelsenDesigns.OneD
