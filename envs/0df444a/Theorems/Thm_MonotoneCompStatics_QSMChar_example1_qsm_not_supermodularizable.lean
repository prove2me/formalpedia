-- Prove2me | Theorems.Thm_MonotoneCompStatics_QSMChar_example1_qsm_not_supermodularizable
-- name    : MonotoneCompStatics.QSMChar.example1_qsm_not_supermodularizable
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:16:28.287073+00:00
-- url     : https://prove2.me/theorems/43b35fbd-3b36-4d13-b49f-4b1a58378731
-- title:
--   Example 1 (p. 165) — a quasisupermodular function that is not supermodularizable
-- statement:
--   Let $f$ be the function of Example 1 on the lattice $X = \{0,1\} \times \{0,1,2,3\}$ with the componentwise order, given by $f(0,\cdot) = (1,2,2,1)$ and $f(1,\cdot) = (3,4,5,3)$. Then
--
--   1. $f$ is quasisupermodular on $X$, and
--   2. $f$ is not supermodularizable: there is no strictly increasing $h : \mathbb{R} \to \mathbb{R}$ such that $h \circ f$ is supermodular on $X$,
--
--   $$
--   \neg\, \exists\, h \text{ strictly increasing}: \ h(f(u)) + h(f(v)) \le h(f(u \vee v)) + h(f(u \wedge v)) \ \ \forall u, v \in X.
--   $$
--
--   The example shows that the converse of the supermodularizability criterion fails, and hence that in Theorem 8 the transformation must be allowed to depend on the sublattice $\{x_1, x_2, x_1 \vee x_2, x_1 \wedge x_2\}$.
--
--   **Formalization Note** "Strictly increasing" is `StrictMono`; with merely nondecreasing $h$ the second claim would be false (take $h$ constant).
-- source:
--   Milgrom and Shannon, Monotone Comparative Statics, Econometrica 62 (1994), p. 165 (PDF p. 10), Example 1

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_MonotoneCompStatics_Monotonicity_QuasiSupermodularOn
import Definitions.Def_MonotoneCompStatics_QSMChar_example1

namespace MonotoneCompStatics.QSMChar

/-- Example 1 (p. 165): the tabulated function on `{0, 1} × {0, 1, 2, 3}` (product order) is
quasisupermodular, but no strictly increasing `h : ℝ → ℝ` makes `h ∘ f` supermodular. -/
theorem example1_qsm_not_supermodularizable :
    MonotoneCompStatics.Monotonicity.QuasiSupermodularOn example1 Set.univ ∧
      ¬ ∃ h : ℝ → ℝ, StrictMono h ∧
        Supermodularity.Monotonicity.SupermodularOn (h ∘ example1) Set.univ := by sorry

end MonotoneCompStatics.QSMChar
