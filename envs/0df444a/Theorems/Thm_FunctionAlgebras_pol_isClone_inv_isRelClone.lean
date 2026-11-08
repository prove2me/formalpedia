-- Prove2me | Theorems.Thm_FunctionAlgebras_pol_isClone_inv_isRelClone
-- name    : FunctionAlgebras.pol_isClone_inv_isRelClone
-- status  : Open
-- author  : @Alien60
-- created : 2026-11-07T16:58:29.861218+00:00
-- url     : https://prove2.me/theorems/bd9da7c2-243c-4b61-b277-f25e59aefc0f
-- title:
--   Pol is a clone and Inv is a co-clone
-- statement:
--   $A$ is a set. For every family of relations $Q$ on $A$, $\mathrm{Pol}\,Q$ (the operations of every arity $n\ge0$ preserving every relation of $Q$) is a clone. For every family of operations $F$ on $A$, $\mathrm{Inv}\,F$ (the relations preserved by every operation of $F$) is a relational clone: it contains every relation definable by a primitive positive formula $\exists\bar y\,\bigwedge_j R_j(\dots)\wedge\bigwedge_l(u_l=v_l)$ with all $R_j$ in $\mathrm{Inv}\,F$.
-- source:
--   D. Lau, Function Algebras on Finite Sets, Springer Monographs in Mathematics, 2006, https://doi.org/10.1007/3-540-36023-9, Part II, Theorem 2.6.2

import Definitions.Def_FunctionAlgebras_defs

universe u

namespace FunctionAlgebras

variable {A : Type u}

/-- Lau, *Function Algebras on Finite Sets*, Part II, Theorem 2.6.2.  For every family of
relations `Q`, the set `Pol Q` of its polymorphisms is a clone, and for every family of
operations `F`, the set `Inv F` of its invariant relations is a relational clone (co-clone). -/
theorem pol_isClone_inv_isRelClone (Q : ∀ h : ℕ, Set (Set (Fin h → A)))
    (F : ∀ n : ℕ, Set ((Fin n → A) → A)) :
    IsClone (Pol Q) ∧ IsRelClone (Inv F) := by sorry

end FunctionAlgebras
