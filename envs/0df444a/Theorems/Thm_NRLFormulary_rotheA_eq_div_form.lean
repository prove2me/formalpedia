-- Prove2me | Theorems.Thm_NRLFormulary_rotheA_eq_div_form
-- name    : NRLFormulary.rotheA_eq_div_form
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T18:02:36.304212+00:00
-- url     : https://prove2.me/theorems/06acf5d4-7114-4c36-87fb-567ff168ccd7
-- title:
--   The Rothe factor: $A_k(x,z)=\frac{x}{x+kz}\binom{x+kz}{k}$ whenever $x+kz\ne 0$
-- statement:
--   **The two forms of the Rothe factor agree off the singular locus.** Let $x, z$ be complex numbers and $k$ a natural number with $x + kz \ne 0$. Then the polynomial form of the Rothe factor equals the quotient form:
--
--   $$A_k(x,z) \;=\; \frac{x}{x+kz}\binom{x+kz}{k},$$
--
--   where $A_0(x,z) = 1$ and $A_k(x,z) = \frac{x(x+kz-1)\cdots(x+kz-k+1)}{k!}$ for $k \ge 1$.
--
--   This is the bridge between the identity as printed in the handbook, whose summands carry the denominator $x+kz$, and the singularity-free form of the identity, whose summands are polynomials. It is exactly the cancellation of the factor $x+kz$ against the leading factor of the falling factorial, and it is what lets a solver transport a proof of the polynomial identity to the printed one.
-- source:
--   J. D. Huba, NRL Plasma Formulary, Naval Research Laboratory, 2013, p. 3, section "Numerical and Algebraic", the Rothe-Hagen identity ("good for all complex x, y, z except when singular"), footnote 2: H. W. Gould, "Note on Some Binomial Coefficient Identities of Rosenbaum", J. Math. Phys. 10, 49 (1969); H. W. Gould and J. Kaucky, "Evaluation of a Class of Binomial Coefficient Summations", J. Comb. Theory 1, 233 (1966). https://www.nrl.navy.mil/News-Media/Publications/NRL-Plasma-Formulary/

import Mathlib
import Definitions.Def_NRLFormulary_cbinom
import Definitions.Def_NRLFormulary_rotheA

namespace NRLFormulary
theorem rotheA_eq_div_form (x z : ℂ) (k : ℕ) (h : x + (k : ℂ) * z ≠ 0) :
    rotheA x z k = x / (x + (k : ℂ) * z) * cbinom (x + (k : ℂ) * z) k := by sorry
end NRLFormulary
