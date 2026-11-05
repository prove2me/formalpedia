-- Prove2me | Theorems.Thm_HardyFLocal_eq24_general_chain
-- name    : HardyFLocal.eq24_general_chain
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:39:28.608881+00:00
-- url     : https://prove2.me/theorems/fed5fde7-c627-4492-8a04-24c1ac5320ba
-- title:
--   Eq. (24), p.13 (corrected: upper indices $k'''k''k'k$), and the general chain
-- statement:
--   Let $\$_k$ be a fiducial family and $\Lambda$ its pair table.
--
--   1. For four sequential vertices, the coordinate at $k$ of $\$_{l'''}\circ\$_{l''}\circ\$_{l'}\circ\$_l$ is
--   $$\sum_{n''\in\Omega^2}\sum_{n'\in\Omega^2}\Lambda^{1\,n''}_{l'''l''}\,\Lambda^{1\,n'}_{n''l'}\,\Lambda^{1\,k}_{n'l}.$$
--   2. For every list $l_1,\dots,l_r$ of labels in time order, the composite $\$_{l_r}\circ\cdots\circ\$_{l_1}$ equals $\sum_k c_k\$_k$, where $c$ is the chain vector computed by the recursion from the pair table, and these real coefficients are unique.
--
--   The second part is the paper's "and so on": a clump of any length is handled by the two tables of (28).
--
--   Differences from the source:
--   - correction: the left side of (24) has lower indices l‴l″l′l and upper indices k″k′k, while the right side has the free index k‴ → the upper indices are k‴k″k′k, and k‴ is 1; reason: the printed equation has k‴ unbound and so is not well formed; this is the four-vertex analogue of (23)
--   - reading: a "fiducial spanning set of superoperators", with Λ in "a real vector space" (p.9) → a basis over ℝ of the Hermiticity-preserving one-qubit maps; reason: real coefficients are what p.9 requires, and they exist for Hermiticity-preserving maps
--   - encoding: labels run from 1, and the first element of Ω² is 1 → labels are 0-based, and the first element of Ω² = Fin 16 is 0; reason: Lean convention; same instances
-- source:
--   L. Hardy, Formalism Locality in Quantum Theory and Quantum Gravity, arXiv:0804.0054v1, §5, eq. (24), p.13

import Mathlib
import Definitions.Def_HardyFLocal_Superoperator
import Definitions.Def_HardyFLocal_FiducialFamily

set_option autoImplicit false

namespace HardyFLocal

/-- **Eq. (24) (corrected: the upper indices are `k''' k'' k' k`), and its generalizations**, Hardy,
arXiv:0804.0054v1, §5, eq. (24), p.13 ("For four sequential vertices, … and so on").

1. For four sequential vertices, the `k` coordinate of `$_{l'''} ∘ $_{l''} ∘ $_{l'} ∘ $_l` is
   `Σ_{n''} Σ_{n'} Λ^{1 n''}_{l''' l''} Λ^{1 n'}_{n'' l'} Λ^{1 k}_{n' l}`, with `Λ = pairTable S`.
2. For every list of labels in time order, the composite is `Σ_k c_k $_k`, where `c` is the vector
   `chainConst (pairTable S) ls` computed by the recursion, and these coefficients are unique.

**Formalization Note** The printed left side of (24) has lower indices `l''' l'' l' l` and upper
indices `k'' k' k`, leaving the right side's `k'''` unbound; the upper indices are read as
`k''' k'' k' k`. -/
theorem eq24_general_chain (S : FiducialFamily) :
    (∀ l''' l'' l' l k : Ω,
      coordsOf S.map (S.map l''' ∘ₗ S.map l'' ∘ₗ S.map l' ∘ₗ S.map l) k =
        ∑ a, ∑ b, pairTable S l''' l'' a * pairTable S a l' b * pairTable S b l k) ∧
    ∀ ls : List Ω,
      compose S ls = ∑ k, chainConst (pairTable S) ls k • S.map k ∧
      ∀ c : Ω → ℝ, compose S ls = ∑ k, c k • S.map k → c = chainConst (pairTable S) ls := by sorry

end HardyFLocal
