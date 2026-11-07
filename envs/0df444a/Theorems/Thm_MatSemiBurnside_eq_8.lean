-- Prove2me | Theorems.Thm_MatSemiBurnside_eq_8
-- name    : MatSemiBurnside.eq_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:38:34.189257+00:00
-- url     : https://prove2.me/theorems/cccef85f-24a3-4133-88d8-931737358052
-- title:
--   Eq. (8): $\rho(bc)\le\min\{\rho(b),\rho(c)\}$
-- statement:
--   Let $d$ be a positive integer, $X\subseteq\mathrm{Mat}_d(\mathbb Q)$ finite and nonempty and $\sim$ a congruence on $\langle X\rangle$. For classes $b,c$ of $\langle X\rangle/\sim$, with $\rho$ the minimum rank of a class,
--   $$\rho(bc)\le\min\{\rho(b),\rho(c)\}.$$
--
--   In particular every factor of a product whose class has minimum rank $r$ belongs to a class of minimum rank at least $r$; this drives the decomposition (9).
--
--   Differences from the source:
--   - encoding: ρ(c) = min{rank(a) : a ∈ c} → `minRank c q`, the `sInf` of the ranks of the elements of the class; reason: classes are nonempty, so the infimum is the minimum
-- source:
--   Guttenberg, Lhote, Shirmohammadi, Worrell, Burnside Problems for Matrix Semigroup Quotients with Applications to Border Complexity, STOC 2027 submission (held version, sha256 1bc61d4e…), Appendix B, proof of Theorem 1, eq. (8), p.30

import Mathlib
import Definitions.Def_MatSemiBurnside_minRank
set_option autoImplicit false

namespace MatSemiBurnside

/-- **Eq. (8).** Guttenberg, Lhote, Shirmohammadi, Worrell, *Burnside Problems for Matrix Semigroup Quotients
with Applications to Border Complexity*, STOC 2027 submission (held version, sha256 1bc61d4e…), Appendix B, proof of Theorem 1, eq. (8), p.30: "Choosing a minimum-rank
representative of either of two classes shows that ρ(bc) ≤ min{ρ(b), ρ(c)}." Here ρ(c) is the
minimum rank of a matrix in the class c (`minRank`) and bc is the product in ⟨X⟩/∼.

**Formalization Note.** Stated for every finite nonempty X (the standing assumption of Appendix B)
and every congruence; the standing bound N is not used by (8) and is not assumed. -/
theorem eq_8 {d : ℕ} (hd : 0 < d) (X : Finset (Matrix (Fin d) (Fin d) ℚ)) (hX : X.Nonempty)
    (c : Con (Subsemigroup.closure (X : Set (Matrix (Fin d) (Fin d) ℚ)))) (b b' : c.Quotient) :
    minRank c (b * b') ≤ min (minRank c b) (minRank c b') := by sorry

end MatSemiBurnside
