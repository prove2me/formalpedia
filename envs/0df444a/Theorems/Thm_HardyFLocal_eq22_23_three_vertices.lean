-- Prove2me | Theorems.Thm_HardyFLocal_eq22_23_three_vertices
-- name    : HardyFLocal.eq22_23_three_vertices
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T06:39:16.547804+00:00
-- url     : https://prove2.me/theorems/70ae015d-17b2-4e20-907b-7e5fa3dbe38d
-- title:
--   Eqs. (22)–(23), p.13 — three sequential vertices
-- statement:
--   Let $\$_k$ be a fiducial family and $\Lambda$ its pair table. For labels $l'',l',l$, the composite $\$_{l''}\circ\$_{l'}\circ\$_l$ has the unique real expansion in $\$_k$ with coefficients
--   $$\Lambda^{1\,1\,k}_{l''l'l}=\sum_{n'\in\Omega^2}\Lambda^{1\,n'}_{l''l'}\,\Lambda^{1\,k}_{n'l}.$$
--   The same coefficients give the printed form (22), a sum over $\{1\}\times\{1\}\times\Omega^2$ of $\$_{k''}\circ\$_{k'}\circ\$_k$.
--
--   So the matrix of a clump of three is computed from the pair table alone.
--
--   Differences from the source:
--   - reading: (22) prints $k″ $k′ ◦ $k with one ◦ missing → $k″ ◦ $k′ ◦ $k; reason: typographic; (21) and the left side of (22) are compositions
--   - reading: a "fiducial spanning set of superoperators", with Λ in "a real vector space" (p.9) → a basis over ℝ of the Hermiticity-preserving one-qubit maps; reason: real coefficients are what p.9 requires, and they exist for Hermiticity-preserving maps
--   - encoding: labels run from 1, and the first element of Ω² is 1 → labels are 0-based, and the first element of Ω² = Fin 16 is 0; reason: Lean convention; same instances
-- source:
--   L. Hardy, Formalism Locality in Quantum Theory and Quantum Gravity, arXiv:0804.0054v1, §5, eqs. (22)–(23), p.13

import Mathlib
import Definitions.Def_HardyFLocal_Superoperator
import Definitions.Def_HardyFLocal_FiducialFamily

set_option autoImplicit false

namespace HardyFLocal

/-- **Eqs. (22)–(23): three sequential vertices**, Hardy, arXiv:0804.0054v1, §5, eqs. (22)–(23), p.13
("It can be shown that, for three sequential vertices, …").

For all `l'', l', l`, the composite `$_{l''} ∘ $_{l'} ∘ $_l` has the unique expansion `Σ_k c_k $_k`
with `c_k = Σ_{n'} Λ^{1 n'}_{l'' l'} Λ^{1 k}_{n' l}` ((23), with `Λ = pairTable S`); and it has the
same coefficients in the printed form (22), a sum over `{1} × {1} × Ω²` of `$_{k''} ∘ $_{k'} ∘ $_k`.

**Formalization Note** Printed (22) omits one `∘` in `$_{k''} $_{k'} ∘ $_k`; it is read as a
composition. -/
theorem eq22_23_three_vertices (S : FiducialFamily) (l'' l' l : Ω) :
    S.map l'' ∘ₗ S.map l' ∘ₗ S.map l =
      ∑ k, (∑ a, pairTable S l'' l' a * pairTable S a l k) • S.map k ∧
    (∀ k, coordsOf S.map (S.map l'' ∘ₗ S.map l' ∘ₗ S.map l) k =
      ∑ a, pairTable S l'' l' a * pairTable S a l k) ∧
    (∀ c : Ω → ℝ, S.map l'' ∘ₗ S.map l' ∘ₗ S.map l = ∑ k, c k • S.map k →
      ∀ k, c k = ∑ a, pairTable S l'' l' a * pairTable S a l k) ∧
    S.map l'' ∘ₗ S.map l' ∘ₗ S.map l =
      ∑ p ∈ ({0} : Finset Ω) ×ˢ ({0} : Finset Ω) ×ˢ (Finset.univ : Finset Ω),
        (∑ a, pairTable S l'' l' a * pairTable S a l p.2.2) •
          (S.map p.1 ∘ₗ S.map p.2.1 ∘ₗ S.map p.2.2) := by sorry

end HardyFLocal
