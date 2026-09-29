-- Prove2me | Theorems.Thm_InverseGalois_inverse_galois_problem_cyclic
-- name    : InverseGalois.inverse_galois_problem_cyclic
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T02:07:13.344551+00:00
-- url     : https://prove2.me/theorems/dd96c174-b07e-47a3-8c0e-df971717c243
-- title:
--   Cyclic groups are realizable over $\mathbb{Q}$
-- statement:
--   Every finite **cyclic** group $G$ is the Galois group of a Galois extension of $\mathbb{Q}$.
--
--   Classically this is obtained from cyclotomic fields: given $n \ge 1$, Dirichlet's theorem on arithmetic progressions supplies a prime $p \equiv 1 \pmod n$; the cyclotomic field $\mathbb{Q}(\mu_p)$ has Galois group cyclic of order $p-1$ over $\mathbb{Q}$, and the fixed field of its subgroup of order $(p-1)/n$ is a Galois extension of $\mathbb{Q}$ with group $\mathbb{Z}/n\mathbb{Z}$.
-- source:
--   Inverse Galois problem, Wikipedia, https://en.wikipedia.org/wiki/Inverse_Galois_problem (revision of 13 September 2026)

import Mathlib
import Definitions.Def_InverseGalois_realizability

namespace InverseGalois

theorem inverse_galois_problem_cyclic
    {G : Type*} [Fintype G] [Group G] [IsCyclic G] :
    IsRealizable ℚ G := by sorry

end InverseGalois
