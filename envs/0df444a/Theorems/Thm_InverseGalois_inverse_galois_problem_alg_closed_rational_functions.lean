-- Prove2me | Theorems.Thm_InverseGalois_inverse_galois_problem_alg_closed_rational_functions
-- name    : InverseGalois.inverse_galois_problem_alg_closed_rational_functions
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-13T02:22:47.729905+00:00
-- url     : https://prove2.me/theorems/f47da782-f919-4e28-8b27-acad63268be8
-- title:
--   Every finite group is realizable over $K(t)$, $K$ algebraically closed of characteristic $0$
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $0$. Then every finite group $G$ is the Galois group of a Galois extension of the rational function field $K(t)$.
--
--   This generalizes the case $K = \mathbb{C}$; the hypotheses "algebraically closed" and "characteristic $0$" are both used, and dropping algebraic closure makes the statement (for $K = \mathbb{Q}$) equivalent to the open inverse Galois problem itself.
-- source:
--   Inverse Galois problem, Wikipedia, https://en.wikipedia.org/wiki/Inverse_Galois_problem (revision of 13 September 2026)

import Mathlib
import Definitions.Def_InverseGalois_realizability

namespace InverseGalois

theorem inverse_galois_problem_alg_closed_rational_functions
    {K G : Type*} [Field K] [IsAlgClosed K] [CharZero K] [Fintype G] [Group G] :
    IsRealizable (RatFunc K) G := by sorry

end InverseGalois
