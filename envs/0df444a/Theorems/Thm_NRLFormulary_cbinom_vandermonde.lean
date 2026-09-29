-- Prove2me | Theorems.Thm_NRLFormulary_cbinom_vandermonde
-- name    : NRLFormulary.cbinom_vandermonde
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T17:57:36.937598+00:00
-- url     : https://prove2.me/theorems/c2afbcd1-0e1d-4518-928b-65218daed89e
-- title:
--   Vandermonde convolution over $\mathbb{C}$: $\sum_{k=0}^{n}\binom{x}{k}\binom{y}{n-k}=\binom{x+y}{n}$
-- statement:
--   **Vandermonde convolution with complex parameters.** For all complex numbers $x, y$ and every natural number $n$,
--
--   $$\sum_{k=0}^{n} \binom{x}{k}\binom{y}{n-k} \;=\; \binom{x+y}{n},$$
--
--   with $\binom{w}{m} = \frac{1}{m!}\prod_{j=0}^{m-1}(w-j)$.
--
--   This is the case $z = 0$ of the Rothe-Hagen identity, and the classical convolution identity for binomial coefficients extended from natural-number to complex upper indices. It is the natural first milestone of the mission: it needs the same complex-upper-index machinery as the goal but none of the Rothe factor's cancellation, and it is the base case against which any polynomial-identity argument for the general statement is calibrated.
-- source:
--   J. D. Huba, NRL Plasma Formulary, Naval Research Laboratory, 2013, p. 3, section "Numerical and Algebraic", the Rothe-Hagen identity ("good for all complex x, y, z except when singular"), footnote 2: H. W. Gould, "Note on Some Binomial Coefficient Identities of Rosenbaum", J. Math. Phys. 10, 49 (1969); H. W. Gould and J. Kaucky, "Evaluation of a Class of Binomial Coefficient Summations", J. Comb. Theory 1, 233 (1966). https://www.nrl.navy.mil/News-Media/Publications/NRL-Plasma-Formulary/

import Mathlib
import Definitions.Def_NRLFormulary_cbinom

namespace NRLFormulary
theorem cbinom_vandermonde (x y : ℂ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), cbinom x k * cbinom y (n - k) = cbinom (x + y) n := by sorry
end NRLFormulary
