-- Prove2me | Theorems.Thm_InverseGalois_inverse_galois_problem_abelian
-- name    : InverseGalois.inverse_galois_problem_abelian
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T02:09:52.31698+00:00
-- url     : https://prove2.me/theorems/66826749-6f7f-4006-b4c0-807612c76b91
-- title:
--   Abelian groups are realizable over $\mathbb{Q}$
-- statement:
--   Every finite **abelian** group $G$ is the Galois group of a Galois extension of $\mathbb{Q}$.
--
--   Here $G$ is a finite type with a commutative group structure. The classical proof extends the cyclic construction: every finite abelian group occurs as a quotient of the Galois group of a suitable cyclotomic extension of $\mathbb{Q}$, and the fixed field of the corresponding subgroup realizes it.
-- source:
--   Inverse Galois problem, Wikipedia, https://en.wikipedia.org/wiki/Inverse_Galois_problem (revision of 13 September 2026)

import Mathlib
import Definitions.Def_InverseGalois_realizability

namespace InverseGalois

theorem inverse_galois_problem_abelian
    {G : Type*} [Fintype G] [CommGroup G] :
    IsRealizable ℚ G := by sorry

end InverseGalois
