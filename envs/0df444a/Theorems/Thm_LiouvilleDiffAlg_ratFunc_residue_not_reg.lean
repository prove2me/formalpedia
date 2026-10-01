-- Prove2me | Theorems.Thm_LiouvilleDiffAlg_ratFunc_residue_not_reg
-- name    : LiouvilleDiffAlg.ratFunc_residue_not_reg
-- status  : Proved
-- author  : @vebis
-- created : 2026-10-01T11:41:24.727866+00:00
-- url     : https://prove2.me/theorems/0ef273ee-fb90-48a5-8cab-4a6fc83738a0
-- title:
--   A simple pole is not regular
-- statement:
--   Let $K$ be a field and $p,q\in K[X]$ with $p$ irreducible and $p\nmid q$. Let $c\in K$ be nonzero. Then the rational function $c\,q/p$ has a genuine pole at $p$: there are no polynomials $a,b$ with $p\nmid b$ and $c\,\dfrac{q}{p}\,b=a$ in $K(X)$.
--
--   This says that a nonzero multiple of a function $q/p$ with a simple pole cannot be rewritten with a denominator coprime to $p$.
--
--   **Formalization Note** The statement is purely algebraic; $c$ is viewed in $K(X)$ via the canonical embedding.
-- source:
--   Rosenlicht, Integration in finite terms, Amer. Math. Monthly 79 (1972), 963–972 (proof of Liouville's theorem by induction on an elementary tower); Geddes–Czapor–Labahn, Algorithms for Computer Algebra (Kluwer, 1992), §12.4; Wikipedia, "Liouville's theorem (differential algebra)", oldid=1349223559, section "Basic theorem"

import Mathlib

open scoped Differential
open Polynomial

namespace LiouvilleDiffAlg

theorem ratFunc_residue_not_reg {K : Type*} [Field K] {p q : K[X]} (hp : Irreducible p)
    (hpq : ¬ p ∣ q) {c : K} (hc : c ≠ 0) :
    ¬ ∃ a b : K[X], ¬ p ∣ b ∧ algebraMap K (RatFunc K) c * (algebraMap K[X] (RatFunc K) q / algebraMap K[X] (RatFunc K) p) * algebraMap K[X] (RatFunc K) b = algebraMap K[X] (RatFunc K) a := by sorry

end LiouvilleDiffAlg
