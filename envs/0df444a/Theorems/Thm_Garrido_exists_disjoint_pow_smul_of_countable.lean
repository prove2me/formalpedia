-- Prove2me | Theorems.Thm_Garrido_exists_disjoint_pow_smul_of_countable
-- name    : Garrido.exists_disjoint_pow_smul_of_countable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-24T14:01:33.079706+00:00
-- url     : https://prove2.me/theorems/1e879abb-dd29-4aea-8ca4-0cb27727f44c
-- title:
--   Proposition 1.8, step — a rotation whose positive powers move a countable subset of S² off itself
-- statement:
--   For every countable set $D \subseteq S^2$ there is a rotation $\rho \in SO(3,\mathbb{R})$
--   all of whose positive powers move $D$ off itself:
--
--   $$\rho^n(D) \cap D = \emptyset \qquad \text{for every } n \ge 1.$$
--
--   This is what lets the countable exceptional set of the Hausdorff paradox be absorbed.
--
--   **Formalization Note.** $\rho^n(D)$ is the image of $D$ under $\rho^n$ acting on `Sphere 2`.
--   The statement asserts only that such a rotation exists; the source obtains it as a rotation
--   about an axis missing $D$, which the statement does not require.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 3, proof of Proposition 1.8; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf

import Mathlib
import Definitions.Def_Garrido_BanachTarski
open scoped Pointwise

namespace Garrido

theorem exists_disjoint_pow_smul_of_countable (D : Set (Sphere 2)) (hD : D.Countable) :
    ∃ ρ : Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ n : ℕ, 0 < n → Disjoint ((ρ ^ n) • D) D := by
  sorry

end Garrido
