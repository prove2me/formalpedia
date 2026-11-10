-- Prove2me | Theorems.Thm_IntegerMatrixMortality_FixedImage_program_matrix_reachability
-- name    : IntegerMatrixMortality.FixedImage.program_matrix_reachability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:33:47.149161+00:00
-- url     : https://prove2.me/theorems/f7004c4c-ecc4-42f4-8d71-e9f9ea2f34a2
-- title:
--   Theorem 5.5 — Program and matrix reachability equivalence
-- statement:
--   Let P₀ be any finite arithmetic program, and allocate a module satisfying the three requirements to every edge occurrence, with private intermediate phases and all labels below N. For any prime p≥7 with p>6N, evaluate the edge formulas and take their finite set G. Every matrix of G is nonsingular with determinant p or −p. For all program states q,r and all n,k∈ℕ,
--
--   $$(q,n)\longrightarrow_{P_0}^*(r,k)\iff\exists W\in G^*,\quad W(C_q(z_n))=C_r(z_k).$$
--
--   The right side ranges over unrestricted matrix words. Duplicated edge matrices, coincident boundaries and the empty word are all allowed.
--
--   Differences from the source:
--   - encoding: rational projective points, residues and matrix words → Option ℚ with explicit poles, reduced-denominator congruence and reversed list products; reason: infinity and empty words have their source values
-- source:
--   Thanin Quartz, Ivan O. Shevchenko, Hans De Sterck, Jun Liu, STOC 2027 submission #1062 (October 2026), Theorem 5.5, PDF p. 11 / printed p. 9

import Definitions.Def_IntegerMatrixMortality_FixedImage_ScanInterfaces

set_option autoImplicit false

namespace IntegerMatrixMortality.FixedImage

theorem program_matrix_reachability
    (P₀ : ArithmeticProgram) (ms : List InstructionModule) (N p : ℕ)
    (ha : ModuleAllocation P₀ ms N)
    (hm : ∀ (i : ℕ) (e : ArithmeticEdge) (M : InstructionModule),
      P₀.edges[i]? = some e → ms[i]? = some M → ModuleRequirements M e.update)
    (hp : Nat.Prime p) (hp7 : 7 ≤ p) (hN : 6*N < p) :
      DeterminantsAtPrime (allocatedGenerators p ms) p ∧
      ∀ q ∈ P₀.states, ∀ r ∈ P₀.states, ∀ n k : ℕ,
        programReach P₀ (q,n) (r,k) ↔
          lineReach (Int.castRingHom ℚ) (allocatedGenerators p ms : Set ZMat)
            (encodedConfig p q n) (encodedConfig p r k) := by sorry

end IntegerMatrixMortality.FixedImage
