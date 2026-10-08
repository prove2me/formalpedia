-- Prove2me | Theorems.Thm_MonotoneCompStatics_QSMChar_qsm_of_supermodularizable
-- name    : MonotoneCompStatics.QSMChar.qsm_of_supermodularizable
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:15:14.642973+00:00
-- url     : https://prove2.me/theorems/1acbe4f7-8dbb-4911-be3c-1cb4e31fb2fc
-- title:
--   pp. 164–165 remark — supermodularizable functions are quasisupermodular
-- statement:
--   Let $X$ be a lattice and $f : X \to \mathbb{R}$. Suppose there is a strictly increasing $h : \mathbb{R} \to \mathbb{R}$ such that $h \circ f$ is supermodular on $X$:
--
--   $$
--   h(f(x)) + h(f(y)) \le h(f(x \vee y)) + h(f(x \wedge y)) \qquad \text{for all } x, y \in X.
--   $$
--
--   Then $f$ is quasisupermodular. Functions $f$ admitting such an $h$ are called **supermodularizable** (Li Calzi, 1991).
--
--   This gives the easy sufficient condition for quasisupermodularity: a function becomes eligible for the paper's monotone comparative statics as soon as some reparametrization of its values is supermodular. Theorem 8 sharpens it to a characterization by allowing the transformation to depend on the four-point sublattice.
--
--   **Formalization Note** Supermodularity on $X$ is the published `Supermodularity.Monotonicity.SupermodularOn (h ∘ f) Set.univ`; quasisupermodularity on $X$ is `QuasiSupermodularOn f Set.univ`; "strictly increasing" is `StrictMono`.
-- source:
--   Milgrom and Shannon, Monotone Comparative Statics, Econometrica 62 (1994), pp. 164–165 (PDF pp. 9–10), remark after Theorem 7

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_MonotoneCompStatics_Monotonicity_QuasiSupermodularOn

namespace MonotoneCompStatics.QSMChar

/-- pp. 164–165 (remark after Theorem 7): if some strictly increasing `h : ℝ → ℝ` makes `h ∘ f`
supermodular on the lattice `X` (`f` is supermodularizable), then `f` is quasisupermodular. -/
theorem qsm_of_supermodularizable {X : Type*} [Lattice X] (f : X → ℝ)
    (h : ℝ → ℝ) (hh : StrictMono h)
    (hsm : Supermodularity.Monotonicity.SupermodularOn (h ∘ f) Set.univ) :
    MonotoneCompStatics.Monotonicity.QuasiSupermodularOn f Set.univ := by sorry

end MonotoneCompStatics.QSMChar
