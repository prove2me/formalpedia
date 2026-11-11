-- Prove2me | Theorems.Thm_MongeApprox_Sparsify_eq_4
-- name    : MongeApprox.Sparsify.eq_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:01:55.213911+00:00
-- url     : https://prove2.me/theorems/ecd13a58-4ace-4565-8e34-9da6a430c66d
-- title:
--   (4) — the total curvature telescopes to four corner entries
-- statement:
--   For every $p\times q$ real matrix $M$ with $p,q\ge1$, $\kappa(M)=\sum_{i=0}^{p-2}\sum_{j=0}^{q-2}M^\square_{ij}=M_{0,q-1}+M_{p-1,0}-M_{00}-M_{p-1,q-1}$.
--
--   Differences from the source:
--   - encoding: p × q matrix with rows/columns indexed by [0..p), [0..q); M□ indexed by [0..p−1) × [0..q−1) → `Matrix (Fin p) (Fin q) ℝ`; `density M i j` a function of naturals that is 0 outside [0..p−1) × [0..q−1); reason: Lean convention; same matrices, and positions outside the density matrix have mass zero as in the paper
--   - encoding: a matrix (implicitly with at least one row and one column) → hypotheses 1 ≤ p, 1 ≤ q; reason: only excludes empty matrices, for which M_00 and the condensed representation are undefined
-- source:
--   Gorbachev 2026, Edit Distance Approximation: Subquadratic Factor Three and Monge Approximation Schemes (PDF sha256 b7eeb435…), (4), printed p. 15 (PDF 17)

import Mathlib
import Definitions.Def_MongeApprox_Sparsify_Monge

namespace MongeApprox.Sparsify

/-- (4): the total curvature `κ(M) = Σ_{i=0}^{p−2} Σ_{j=0}^{q−2} M□_ij` of a `p × q` real matrix
telescopes to `M_{0,q−1} + M_{p−1,0} − M_00 − M_{p−1,q−1}`. -/
theorem eq_4 {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (M : Matrix (Fin p) (Fin q) ℝ) :
    totalCurvature M =
      M ⟨0, hp⟩ ⟨q - 1, by omega⟩ + M ⟨p - 1, by omega⟩ ⟨0, hq⟩
        - M ⟨0, hp⟩ ⟨0, hq⟩ - M ⟨p - 1, by omega⟩ ⟨q - 1, by omega⟩ := by sorry

end MongeApprox.Sparsify
