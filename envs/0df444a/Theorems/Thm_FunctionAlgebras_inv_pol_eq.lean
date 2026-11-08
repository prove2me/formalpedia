-- Prove2me | Theorems.Thm_FunctionAlgebras_inv_pol_eq
-- name    : FunctionAlgebras.inv_pol_eq
-- status  : Open
-- author  : @Alien60
-- created : 2026-11-07T16:58:50.731349+00:00
-- url     : https://prove2.me/theorems/1fc57898-9419-49b4-8478-0a9cb2b39fba
-- title:
--   Every co-clone is Inv Pol of itself
-- statement:
--   $A$ is a finite set. Let $Q$ be a relational clone on $A$: a family of relations containing every relation definable by a primitive positive formula $\exists\bar y\,\bigwedge_j R_j(\dots)\wedge\bigwedge_l(u_l=v_l)$ with $R_j\in Q$. Then $\mathrm{Inv}\,\mathrm{Pol}\,Q=Q$, where $\mathrm{Pol}$ includes nullary operations.
-- source:
--   D. Lau, Function Algebras on Finite Sets, Springer Monographs in Mathematics, 2006, https://doi.org/10.1007/3-540-36023-9, Part II, Theorem 2.9.2 (Bodnarcuk-Kaluznin-Kotov-Romov 1969; Geiger 1968)

import Definitions.Def_FunctionAlgebras_defs

universe u

namespace FunctionAlgebras

variable {A : Type u}

/-- Lau, *Function Algebras on Finite Sets*, Part II, Theorem 2.9.2 (Bodnarčuk–Kalužnin–Kotov–
Romov; Geiger).  On a finite set, every relational clone (co-clone) is the set of invariant
relations of its polymorphisms: `Q = Inv Pol Q`. -/
theorem inv_pol_eq [Finite A] (Q : ∀ h : ℕ, Set (Set (Fin h → A))) (hQ : IsRelClone Q) :
    Inv (Pol Q) = Q := by sorry

end FunctionAlgebras
