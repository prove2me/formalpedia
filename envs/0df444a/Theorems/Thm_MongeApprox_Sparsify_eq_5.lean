-- Prove2me | Theorems.Thm_MongeApprox_Sparsify_eq_5
-- name    : MongeApprox.Sparsify.eq_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:02:01.861834+00:00
-- url     : https://prove2.me/theorems/7fd8bc48-3822-4c08-a259-e67d9fc3fd2f
-- title:
--   (5) — the condensed representation determines every entry
-- statement:
--   For every $p\times q$ real matrix $M$ and every entry $(i,j)$, $M_{ij}=M_{i0}+M_{0j}-M_{00}-\sum_{a<i,\,b<j}M^\square_{ab}$; hence the top row, the leftmost column and the core determine $M$.
--
--   Differences from the source:
--   - encoding: p × q matrix with rows/columns indexed by [0..p), [0..q); M□ indexed by [0..p−1) × [0..q−1) → `Matrix (Fin p) (Fin q) ℝ`; `density M i j` a function of naturals that is 0 outside [0..p−1) × [0..q−1); reason: Lean convention; same matrices, and positions outside the density matrix have mass zero as in the paper
-- source:
--   Gorbachev 2026, Edit Distance Approximation: Subquadratic Factor Three and Monge Approximation Schemes (PDF sha256 b7eeb435…), (5), printed p. 15 (PDF 17)

import Mathlib
import Definitions.Def_MongeApprox_Sparsify_Monge

namespace MongeApprox.Sparsify

/-- (5): the condensed representation (top row, leftmost column, core) determines every entry:
`M_ij = M_i0 + M_0j − M_00 − Σ_{a<i, b<j} M□_ab` for every `p × q` real matrix and every entry. -/
theorem eq_5 {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) (i : Fin p) (j : Fin q) :
    M i j = M i ⟨0, j.pos⟩ + M ⟨0, i.pos⟩ j - M ⟨0, i.pos⟩ ⟨0, j.pos⟩
      - ∑ a ∈ Finset.range i, ∑ b ∈ Finset.range j, density M a b := by sorry

end MongeApprox.Sparsify
