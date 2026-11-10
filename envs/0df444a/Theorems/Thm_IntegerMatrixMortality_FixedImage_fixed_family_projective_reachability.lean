-- Prove2me | Theorems.Thm_IntegerMatrixMortality_FixedImage_fixed_family_projective_reachability
-- name    : IntegerMatrixMortality.FixedImage.fixed_family_projective_reachability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:34:29.24587+00:00
-- url     : https://prove2.me/theorems/43ccda1a-26d9-459e-829a-b5561be48537
-- title:
--   Theorem 3.2 — Fixed-family projective reachability
-- statement:
--   There are a fixed prime p, a fixed finite set G of integer two-by-two matrices with determinant p or −p, a fixed rational source s and a computable rational sequence (tρ) such that, for every natural input ρ,
--
--   $$\operatorname{Halts}_U(1,\rho,0)\iff\exists W\in G^*,\quad W(s)=t_\rho.$$
--
--   The family, prime and source are chosen before ρ. The word may be empty and its length is unbounded. This supplies the projective decision problem for rank-one conversion.
--
--   Differences from the source:
--   - encoding: the fixed source machine and reversed program → the full 278-row table, representative quotient, and named reversed program P; reason: the definitions are the source construction, without a universality or simulation premise
--   - encoding: rational projective points, residues and matrix words → Option ℚ with explicit poles, reduced-denominator congruence and reversed list products; reason: infinity and empty words have their source values
-- source:
--   Thanin Quartz, Ivan O. Shevchenko, Hans De Sterck, Jun Liu, STOC 2027 submission #1062 (October 2026), Theorem 3.2, PDF p. 6 / printed p. 4

import Definitions.Def_IntegerMatrixMortality_FixedImage_ScanInterfaces

set_option autoImplicit false

namespace IntegerMatrixMortality.FixedImage

theorem fixed_family_projective_reachability
    : ∃ (p : ℕ) (G : Finset ZMat) (s : ℚ) (t : ℕ → ℚ),
      Nat.Prime p ∧ DeterminantsAtPrime G p ∧ Computable t ∧
      ∀ ρ : ℕ, machineHalts U (1,ρ,0) ↔
        lineReach (Int.castRingHom ℚ) (G : Set ZMat) (some s) (some (t ρ)) := by sorry

end IntegerMatrixMortality.FixedImage
