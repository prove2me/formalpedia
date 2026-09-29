-- Prove2me | Theorems.Thm_NRLFormulary_rotheA_convolution
-- name    : NRLFormulary.rotheA_convolution
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T18:07:28.781766+00:00
-- url     : https://prove2.me/theorems/c92bfb4c-bba3-4e73-9d4d-ca3642e6eca6
-- title:
--   Rothe-Hagen without side conditions: $\sum_{k=0}^{n}A_k(x,z)A_{n-k}(y,z)=A_n(x+y,z)$
-- statement:
--   **Rothe-Hagen identity, singularity-free form.** For all complex numbers $x, y, z$ and every natural number $n$,
--
--   $$\sum_{k=0}^{n} A_k(x,z)\,A_{n-k}(y,z) \;=\; A_n(x+y,z),$$
--
--   where $A_0(x,z) = 1$ and $A_k(x,z) = \frac{x(x+kz-1)(x+kz-2)\cdots(x+kz-k+1)}{k!}$ for $k \ge 1$ is the polynomial form of the Rothe factor $\frac{x}{x+kz}\binom{x+kz}{k}$.
--
--   Because the Rothe factors are polynomials in their parameters, this version of the identity carries no non-vanishing hypotheses at all: it holds on the whole of $\mathbb{C}^3$, including the locus $x + kz = 0$ where the printed form is undefined. Together with the comparison between the two forms of the Rothe factor it implies the mission's goal theorem, and it is the statement a polynomial-identity or generating-function proof is naturally phrased in.
-- source:
--   J. D. Huba, NRL Plasma Formulary, Naval Research Laboratory, 2013, p. 3, section "Numerical and Algebraic", the Rothe-Hagen identity ("good for all complex x, y, z except when singular"), footnote 2: H. W. Gould, "Note on Some Binomial Coefficient Identities of Rosenbaum", J. Math. Phys. 10, 49 (1969); H. W. Gould and J. Kaucky, "Evaluation of a Class of Binomial Coefficient Summations", J. Comb. Theory 1, 233 (1966). https://www.nrl.navy.mil/News-Media/Publications/NRL-Plasma-Formulary/

import Mathlib
import Definitions.Def_NRLFormulary_rotheA

namespace NRLFormulary
theorem rotheA_convolution (x y z : ℂ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), rotheA x z k * rotheA y z (n - k) = rotheA (x + y) z n := by sorry
end NRLFormulary
