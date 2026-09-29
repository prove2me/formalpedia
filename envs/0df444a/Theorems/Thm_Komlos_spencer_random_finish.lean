-- Prove2me | Theorems.Thm_Komlos_spencer_random_finish
-- name    : Komlos.spencer_random_finish
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-08T23:45:42.871254+00:00
-- url     : https://prove2.me/theorems/43497e2c-0916-4c29-b52b-623e0b86d7e5
-- title:
--   Union-bound colouring of a residual set of columns
-- statement:
--   Let $A$ be an $n\times n$ matrix with entries in $\{0,1\}$ and let $T$ be any set of columns. Then some $\pm1$ colouring of $T$ (extended by $0$ elsewhere) satisfies
--
--   $$\Bigl|\sum_{j\in T}A_{ij}\chi_j\Bigr|\;\le\;\sqrt{2|T|\log(4n)}\qquad\text{for every }i .$$
--
--   This is the elementary bound that a single random colouring already achieves, and it is what one uses to dispose of a residual set of columns once it has become small: when $|T|$ has been driven down to $o(n/\log n)$ the right-hand side is $o(\sqrt{n})$ and the residual set costs nothing on the scale of Spencer's bound. Applied with $T$ the whole ground set it gives only the classical $O(\sqrt{n\log n})$, which is the bound Spencer's theorem improves.
--
--   **Formalization Note** The logarithm is taken at $4n$ rather than $2n$ so that the counting bound is strict and a surviving colouring exists; the difference is immaterial for the intended use. Colourings are encoded as real-valued vectors that are $\pm 1$ on $T$ and $0$ off it.
-- source:
--   J. Spencer, Six standard deviations suffice, Trans. Amer. Math. Soc. 289 (1985) 679-706, Theorem 1 and Section 2 (the entropy / partial colouring method), https://doi.org/10.1090/S0002-9947-1985-0784009-0

import Mathlib
open Finset

namespace Komlos

theorem spencer_random_finish
    (n : ℕ) (hn : 0 < n) (A : Fin n → Fin n → ℝ) (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (T : Finset (Fin n)) :
    ∃ χ : Fin n → ℝ,
      (∀ j, j ∈ T → (χ j = 1 ∨ χ j = -1)) ∧
      (∀ j, j ∉ T → χ j = 0) ∧
      (∀ i, |∑ j ∈ T, A i j * χ j|
          ≤ Real.sqrt (2 * (T.card : ℝ) * Real.log (4 * n))) := by sorry

end Komlos
