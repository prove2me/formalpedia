-- Prove2me | Theorems.Thm_InverseGalois_inverse_galois_problem
-- name    : InverseGalois.inverse_galois_problem
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-13T02:01:29.688955+00:00
-- url     : https://prove2.me/theorems/0c9a03fc-5aa5-41fb-8e23-6a8b2f9168c2
-- title:
--   The inverse Galois problem
-- statement:
--   **The inverse Galois problem.** Every finite group $G$ is the Galois group of some Galois extension of the rational numbers: there is a field $L$ with a $\mathbb{Q}$-algebra structure such that $L/\mathbb{Q}$ is Galois and
--   $$ \mathrm{Gal}(L/\mathbb{Q}) \;\cong\; G. $$
--
--   The group $G$ is an arbitrary type carrying a group structure and a finiteness witness; no further hypothesis is assumed. The question, first posed in the early nineteenth century, is open.
-- source:
--   Inverse Galois problem, Wikipedia, https://en.wikipedia.org/wiki/Inverse_Galois_problem (revision of 13 September 2026)

import Mathlib
import Definitions.Def_InverseGalois_realizability

namespace InverseGalois

theorem inverse_galois_problem {G : Type*} [Fintype G] [Group G] :
    IsRealizable ℚ G := by sorry

end InverseGalois
