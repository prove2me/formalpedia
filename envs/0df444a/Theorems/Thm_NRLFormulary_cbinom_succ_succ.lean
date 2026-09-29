-- Prove2me | Theorems.Thm_NRLFormulary_cbinom_succ_succ
-- name    : NRLFormulary.cbinom_succ_succ
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T17:53:38.494006+00:00
-- url     : https://prove2.me/theorems/95d0601a-dbe8-4f57-b1e6-2dbfbcef85b6
-- title:
--   Pascal's rule for a complex upper index: $\binom{w+1}{k+1}=\binom{w}{k}+\binom{w}{k+1}$
-- statement:
--   **Pascal's rule for a complex upper index.** For every complex number $w$ and every natural number $k$,
--
--   $$\binom{w+1}{k+1} \;=\; \binom{w}{k} + \binom{w}{k+1},$$
--
--   where $\binom{w}{m} = \frac{1}{m!}\prod_{j=0}^{m-1}(w-j)$ is the generalized binomial coefficient.
--
--   The rule is the basic recurrence of the binomial coefficients, valid verbatim once the upper index is allowed to be an arbitrary complex number. It is the workhorse of inductive arguments on the lower index and is used repeatedly in the elementary treatments of the Rothe-Hagen identity.
-- source:
--   J. D. Huba, NRL Plasma Formulary, Naval Research Laboratory, 2013, p. 3, section "Numerical and Algebraic", the Rothe-Hagen identity ("good for all complex x, y, z except when singular"), footnote 2: H. W. Gould, "Note on Some Binomial Coefficient Identities of Rosenbaum", J. Math. Phys. 10, 49 (1969); H. W. Gould and J. Kaucky, "Evaluation of a Class of Binomial Coefficient Summations", J. Comb. Theory 1, 233 (1966). https://www.nrl.navy.mil/News-Media/Publications/NRL-Plasma-Formulary/

import Mathlib
import Definitions.Def_NRLFormulary_cbinom

namespace NRLFormulary
theorem cbinom_succ_succ (w : ℂ) (k : ℕ) :
    cbinom (w + 1) (k + 1) = cbinom w k + cbinom w (k + 1) := by sorry
end NRLFormulary
