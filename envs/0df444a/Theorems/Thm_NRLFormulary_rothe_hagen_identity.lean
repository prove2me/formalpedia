-- Prove2me | Theorems.Thm_NRLFormulary_rothe_hagen_identity
-- name    : NRLFormulary.rothe_hagen_identity
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T17:53:13.007509+00:00
-- url     : https://prove2.me/theorems/359a99d4-f55c-4c77-a6dc-f8c6c4b0e094
-- title:
--   Rothe-Hagen identity: $\sum_{k=0}^{n}\frac{x}{x+kz}\binom{x+kz}{k}\frac{y}{y+(n-k)z}\binom{y+(n-k)z}{n-k}=\frac{x+y}{x+y+nz}\binom{x+y+nz}{n}$
-- statement:
--   **Rothe-Hagen identity.** Let $x, y, z$ be complex numbers and $n$ a natural number, and write $\binom{w}{k} = \frac{1}{k!}\prod_{j=0}^{k-1}(w-j)$ for the generalized binomial coefficient with complex upper index. Assume the identity's denominators are all non-zero, namely
--
--   1. $x + kz \ne 0$ for every $0 \le k \le n$,
--   2. $y + kz \ne 0$ for every $0 \le k \le n$,
--   3. $x + y + nz \ne 0$.
--
--   Then
--
--   $$\sum_{k=0}^{n} \frac{x}{x+kz}\binom{x+kz}{k}\;\frac{y}{y+(n-k)z}\binom{y+(n-k)z}{n-k} \;=\; \frac{x+y}{x+y+nz}\binom{x+y+nz}{n}.$$
--
--   This is the identity printed on p. 3 of the *NRL Plasma Formulary*, where it is stated to hold for all complex $x$, $y$, $z$ "except when singular"; the three hypotheses above are that proviso written out. Setting $z = 0$ recovers the Vandermonde convolution, and the identity is the coefficient form of the multiplicativity of the generalized binomial series.
--
--   **Formalization Note.** The sum runs over $k \in \{0, 1, \ldots, n\}$ and the complementary index is the natural-number difference $n - k$, which is the ordinary difference throughout that range.
-- source:
--   J. D. Huba, NRL Plasma Formulary, Naval Research Laboratory, 2013, p. 3, section "Numerical and Algebraic", the Rothe-Hagen identity ("good for all complex x, y, z except when singular"), footnote 2: H. W. Gould, "Note on Some Binomial Coefficient Identities of Rosenbaum", J. Math. Phys. 10, 49 (1969); H. W. Gould and J. Kaucky, "Evaluation of a Class of Binomial Coefficient Summations", J. Comb. Theory 1, 233 (1966). https://www.nrl.navy.mil/News-Media/Publications/NRL-Plasma-Formulary/

import Mathlib
import Definitions.Def_NRLFormulary_cbinom

namespace NRLFormulary
theorem rothe_hagen_identity (x y z : ℂ) (n : ℕ)
    (hx : ∀ k ≤ n, x + (k : ℂ) * z ≠ 0)
    (hy : ∀ k ≤ n, y + (k : ℂ) * z ≠ 0)
    (hxy : x + y + (n : ℂ) * z ≠ 0) :
    ∑ k ∈ Finset.range (n + 1),
        (x / (x + (k : ℂ) * z) * cbinom (x + (k : ℂ) * z) k) *
          (y / (y + ((n - k : ℕ) : ℂ) * z) * cbinom (y + ((n - k : ℕ) : ℂ) * z) (n - k))
      = (x + y) / (x + y + (n : ℂ) * z) * cbinom (x + y + (n : ℂ) * z) n := by sorry
end NRLFormulary
