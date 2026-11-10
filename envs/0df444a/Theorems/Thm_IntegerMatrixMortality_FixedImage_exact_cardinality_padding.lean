-- Prove2me | Theorems.Thm_IntegerMatrixMortality_FixedImage_exact_cardinality_padding
-- name    : IntegerMatrixMortality.FixedImage.exact_cardinality_padding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:35:04.0351+00:00
-- url     : https://prove2.me/theorems/9be80555-c65b-4d18-ac1b-423b679f5448
-- title:
--   Lemma E.1 — Exact cardinality without changing reachability
-- statement:
--   The concrete fixed program P can be implemented with a single fixed prime p and exactly 5798 distinct nonsingular integer two-by-two matrices G, all of determinant p or −p. Reserve 5798 unused phase labels before choosing p>6(N+5798), evaluate the original table and add its deficit using (E.1). For every pair of program configurations,
--
--   $$ (q,n)\longrightarrow_P^*(r,k)\iff\exists W\in G^*,\quad W(C_q(z_n))=C_r(z_k).$$
--
--   Here G is the explicitly defined padded family. Unrestricted matrix reachability is unchanged, including after an unfinished original prefix; neither padding nor the prime depends on the machine input.
--
--   Differences from the source:
--   - encoding: the fixed program implemented by exactly 5798 distinct matrices → the named paddedGenerators family with a finite phase-label upper bound; reason: unused gaps in labels only enlarge the allowable prime choice; all source configurations, words and exact counts are retained
-- source:
--   Thanin Quartz, Ivan O. Shevchenko, Hans De Sterck, Jun Liu, STOC 2027 submission #1062 (October 2026), Lemma E.1, PDF p. 31 / printed p. 29

import Definitions.Def_IntegerMatrixMortality_FixedImage_ScanInterfaces

set_option autoImplicit false

namespace IntegerMatrixMortality.FixedImage

theorem exact_cardinality_padding
    : ∃ p : ℕ, Nat.Prime p ∧ 6*(fixedPhaseBound+5798) < p ∧
      (paddedGenerators p).card = 5798 ∧ DeterminantsAtPrime (paddedGenerators p) p ∧
      ∀ q ∈ P.states, ∀ r ∈ P.states, ∀ n k : ℕ,
        programReach P (q,n) (r,k) ↔
          lineReach (Int.castRingHom ℚ) (paddedGenerators p : Set ZMat)
            (encodedConfig p q n) (encodedConfig p r k) := by sorry

end IntegerMatrixMortality.FixedImage
