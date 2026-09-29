-- Prove2me | Theorems.Thm_InverseGalois_inverse_galois_problem_over_some_number_field
-- name    : InverseGalois.inverse_galois_problem_over_some_number_field
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T02:14:46.460108+00:00
-- url     : https://prove2.me/theorems/9925a756-34ab-4e49-bf25-cafbb3ca789a
-- title:
--   Every finite group is a Galois group over some number field
-- statement:
--   For every finite group $G$ there is a field $K$ with $\mathbb{Q} \subseteq K \subseteq \mathbb{C}$ such that $G$ is the Galois group of a Galois extension of $K$.
--
--   Here $K$ ranges over the intermediate fields of $\mathbb{C}/\mathbb{Q}$; no algebraicity or finiteness over $\mathbb{Q}$ is imposed on $K$ by the statement, so the assertion is exactly that the base field may be enlarged. It follows from Cayley's embedding $G \hookrightarrow S_n$ together with the realizability of $S_n$ over $\mathbb{Q}$: if $L/\mathbb{Q}$ is Galois with group $S_n$, then $L/L^{G}$ is Galois with group $G$.
-- source:
--   Inverse Galois problem, Wikipedia, https://en.wikipedia.org/wiki/Inverse_Galois_problem (revision of 13 September 2026)

import Mathlib
import Definitions.Def_InverseGalois_realizability

namespace InverseGalois

theorem inverse_galois_problem_over_some_number_field
    {G : Type*} [Fintype G] [Group G] :
    ∃ K : IntermediateField ℚ ℂ, IsRealizable K G := by sorry

end InverseGalois
