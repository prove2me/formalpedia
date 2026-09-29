-- Prove2me | Theorems.Thm_InverseGalois_inverse_galois_problem_solvable
-- name    : InverseGalois.inverse_galois_problem_solvable
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-13T02:13:08.353647+00:00
-- url     : https://prove2.me/theorems/ff56a520-baa8-4f09-b05d-e7c7164f97c3
-- title:
--   Shafarevich: solvable groups are realizable over $\mathbb{Q}$
-- statement:
--   Every finite **solvable** group $G$ is the Galois group of a Galois extension of $\mathbb{Q}$.
--
--   Solvability is Mathlib's `Group.IsSolvable G`: the derived series of $G$ reaches the trivial subgroup. This is Shafarevich's theorem, proved by solving embedding problems for splitting extensions.
-- source:
--   Inverse Galois problem, Wikipedia, https://en.wikipedia.org/wiki/Inverse_Galois_problem (revision of 13 September 2026); I. R. Shafarevich, The imbedding problem for splitting extensions, Dokl. Akad. Nauk SSSR 120 (1958), 1217–1219

import Mathlib
import Definitions.Def_InverseGalois_realizability

namespace InverseGalois

theorem inverse_galois_problem_solvable
    {G : Type*} [Fintype G] [Group G] [Group.IsSolvable G] :
    IsRealizable ℚ G := by sorry

end InverseGalois
