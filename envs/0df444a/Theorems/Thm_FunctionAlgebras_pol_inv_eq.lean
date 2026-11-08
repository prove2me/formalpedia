-- Prove2me | Theorems.Thm_FunctionAlgebras_pol_inv_eq
-- name    : FunctionAlgebras.pol_inv_eq
-- status  : Open
-- author  : @Alien60
-- created : 2026-11-07T16:58:39.898773+00:00
-- url     : https://prove2.me/theorems/b18feaa4-8713-4733-a95f-5975245c9f7a
-- title:
--   Every clone is Pol Inv of itself
-- statement:
--   $A$ is a set; operations are maps $A^n\to A$ ($n\ge0$). $C=(C_n)_n$ is a clone: it contains all projections and is closed under composition $f(g_0,\dots,g_{n-1})$. If $A$ is finite, then $\mathrm{Pol}\,\mathrm{Inv}\,C=C$.
-- source:
--   D. Lau, Function Algebras on Finite Sets, Springer Monographs in Mathematics, 2006, https://doi.org/10.1007/3-540-36023-9, Part II, Theorem 2.9.1

import Definitions.Def_FunctionAlgebras_defs

universe u

namespace FunctionAlgebras

variable {A : Type u}

/-- Lau, *Function Algebras on Finite Sets*, Part II, Theorem 2.9.1.  On a finite set, every
clone is the set of polymorphisms of its invariant relations: `C = Pol Inv C`. -/
theorem pol_inv_eq [Finite A] (C : ∀ n : ℕ, Set ((Fin n → A) → A)) (hC : IsClone C) :
    Pol (Inv C) = C := by sorry

end FunctionAlgebras
