-- Prove2me | Theorems.Thm_MatchVec3_support_bound
-- name    : MatchVec3.support_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:42:09.173366+00:00
-- url     : https://prove2.me/theorems/d212aedf-c809-4bab-a79b-205d11f58bf6
-- title:
--   §2.1: the support bound on min-entropy
-- statement:
--   For a finitely supported random variable $X$,
--
--   $$H_\infty(X)\le\log|\mathrm{supp}(X)|.$$
--
--   In particular, if $X$ takes values in $\mathbb Z^n_m$ then $H_\infty(X)\le n\log m$.
--
--   This is the upper bound on the entropy of the random sum.
--
--   Differences from the source:
--   - encoding: a modulus m → m ≠ 0; reason: ZMod 0 is ℤ, which is not a modulus
-- source:
--   Aggarwal, Obremski, Subexponential Upper Bounds for 3-Restricted Matching Vector Families, STOC 2027 submission (manuscript sha256 44199413…), §2.1, p.8

import Mathlib
import Definitions.Def_MatchVec3_minEntropy

namespace MatchVec3

/-- **The support bound** (Aggarwal, Obremski, STOC 2027 submission (manuscript sha256 44199413…), §2.1,
p.8): `H∞(X) ≤ log |supp(X)|` for a finitely supported `X`; in particular `H∞(X) ≤ n log m` if `X` takes
values in `Z_m^n`.

**Formalization Note** The first clause is for a value type in any universe. `m ≠ 0` says that `m` is a modulus; `ZMod 0 = ℤ` is not finite. -/
theorem support_bound.{u} :
    (∀ {α : Type u} (X : PMF α), X.support.Finite → minEntropy X ≤ Real.log X.support.ncard) ∧
    (∀ {m n : ℕ}, m ≠ 0 → ∀ X : PMF (Fin n → ZMod m), minEntropy X ≤ n * Real.log m) := by sorry

end MatchVec3
