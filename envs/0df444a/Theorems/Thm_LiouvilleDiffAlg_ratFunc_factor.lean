-- Prove2me | Theorems.Thm_LiouvilleDiffAlg_ratFunc_factor
-- name    : LiouvilleDiffAlg.ratFunc_factor
-- status  : Proved
-- author  : @vebis
-- created : 2026-10-01T11:41:23.596508+00:00
-- url     : https://prove2.me/theorems/7fc1bcef-5a0d-48af-b644-db4300609f4b
-- title:
--   Prime factorization of a rational function
-- statement:
--   Let $K$ be a field and $u\in K(X)$ a nonzero rational function. Then there exist a nonzero constant $a\in K$ and finite multisets $N,D$ of monic irreducible polynomials in $K[X]$ such that
--
--   $$u = a\,\frac{\prod_{p\in N}p}{\prod_{p\in D}p}.$$
--
--   This is the factorization of a rational function into its leading constant and its prime factors, with multiplicities.
--
--   **Formalization Note** Multisets of polynomials record the multiplicities of the prime factors.
-- source:
--   Rosenlicht, Integration in finite terms, Amer. Math. Monthly 79 (1972), 963–972 (proof of Liouville's theorem by induction on an elementary tower); Geddes–Czapor–Labahn, Algorithms for Computer Algebra (Kluwer, 1992), §12.4; Wikipedia, "Liouville's theorem (differential algebra)", oldid=1349223559, section "Basic theorem"

import Mathlib

open scoped Differential
open Polynomial

namespace LiouvilleDiffAlg

theorem ratFunc_factor {K : Type*} [Field K] (u : RatFunc K) (hu : u ≠ 0) :
    ∃ (a : K) (N D : Multiset K[X]), a ≠ 0 ∧ (∀ p ∈ N, Monic p ∧ Irreducible p) ∧
      (∀ p ∈ D, Monic p ∧ Irreducible p) ∧
      u = algebraMap K (RatFunc K) a * algebraMap K[X] (RatFunc K) N.prod / algebraMap K[X] (RatFunc K) D.prod := by sorry

end LiouvilleDiffAlg
