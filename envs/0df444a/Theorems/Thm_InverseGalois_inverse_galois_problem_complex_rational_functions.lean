-- Prove2me | Theorems.Thm_InverseGalois_inverse_galois_problem_complex_rational_functions
-- name    : InverseGalois.inverse_galois_problem_complex_rational_functions
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-13T02:21:31.922402+00:00
-- url     : https://prove2.me/theorems/603a8fc3-95d5-42c0-81bd-1928ede549e5
-- title:
--   Every finite group is realizable over $\mathbb{C}(t)$
-- statement:
--   Every finite group $G$ is the Galois group of a Galois extension of the field $\mathbb{C}(t)$ of rational functions in one variable with complex coefficients.
--
--   This is the function-field form of the Riemann existence theorem: finite groups are realized as deck transformation groups of branched covers of the Riemann sphere, and the corresponding function-field extensions are Galois with the prescribed group.
-- source:
--   Inverse Galois problem, Wikipedia, https://en.wikipedia.org/wiki/Inverse_Galois_problem (revision of 13 September 2026)

import Mathlib
import Definitions.Def_InverseGalois_realizability

namespace InverseGalois

theorem inverse_galois_problem_complex_rational_functions
    {G : Type*} [Fintype G] [Group G] :
    IsRealizable (RatFunc ℂ) G := by sorry

end InverseGalois
