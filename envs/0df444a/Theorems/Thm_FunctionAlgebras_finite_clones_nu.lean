-- Prove2me | Theorems.Thm_FunctionAlgebras_finite_clones_nu
-- name    : FunctionAlgebras.finite_clones_nu
-- status  : Open
-- author  : @Alien60
-- created : 2026-11-07T16:59:43.908548+00:00
-- url     : https://prove2.me/theorems/185d08ad-5b8e-46bf-a3f9-42951ad2d1d3
-- title:
--   Finitely many clones contain a near-unanimity operation
-- statement:
--   $A$ is a finite set and $d\ge2$. The set of clones on $A$ (families $C=(C_n)_{n\ge0}$ containing all projections and closed under composition) that contain a $(d+1)$-ary near-unanimity operation is finite.
-- source:
--   D. Lau, Function Algebras on Finite Sets, Springer Monographs in Mathematics, 2006, https://doi.org/10.1007/3-540-36023-9, Part II, Theorem 8.3.1 (second clause)

import Definitions.Def_FunctionAlgebras_defs

universe u

namespace FunctionAlgebras

variable {A : Type u}

/-- Lau, *Function Algebras on Finite Sets*, Part II, Theorem 8.3.1 (second clause).  On a finite
set, for fixed `d ≥ 2` there are only finitely many clones containing a `(d+1)`-ary
near-unanimity operation. -/
theorem finite_clones_nu [Finite A] {d : ℕ} (hd : 2 ≤ d) :
    {C : ∀ n : ℕ, Set ((Fin n → A) → A) |
      IsClone C ∧ ∃ m ∈ C (d + 1), IsNearUnanimity m}.Finite := by sorry

end FunctionAlgebras
