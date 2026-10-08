-- Prove2me | Theorems.Thm_MonotoneCompStatics_QSMChar_qsm_comp_strictMono
-- name    : MonotoneCompStatics.QSMChar.qsm_comp_strictMono
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:13:44.476973+00:00
-- url     : https://prove2.me/theorems/a7e0819a-fd1f-4c6c-b999-7f0a94700ecd
-- title:
--   p. 164 remark — a strictly increasing transformation of a quasisupermodular function is quasisupermodular
-- statement:
--   Let $X$ be a lattice and let $f : X \to \mathbb{R}$ be quasisupermodular: for all $x, y \in X$, $f(x) \ge (>)\, f(x \wedge y)$ implies $f(x \vee y) \ge (>)\, f(y)$. Let $g : \mathbb{R} \to \mathbb{R}$ be strictly increasing. Then the composition
--
--   $$
--   g \circ f : X \to \mathbb{R}, \qquad x \mapsto g(f(x)),
--   $$
--
--   is also quasisupermodular.
--
--   The statement says that quasisupermodularity is an ordinal property: it is invariant under every strictly increasing change of the units of the objective. This is what separates it from supermodularity, which is not preserved by such transformations.
--
--   **Formalization Note** Quasisupermodularity on $X$ is `QuasiSupermodularOn f Set.univ`; "strictly increasing" is `StrictMono`. The page states the remark for functions on the whole lattice, and so does the formal statement.
-- source:
--   Milgrom and Shannon, Monotone Comparative Statics, Econometrica 62 (1994), p. 164 (PDF p. 9), remark after Theorem 7

import Mathlib
import Definitions.Def_MonotoneCompStatics_Monotonicity_QuasiSupermodularOn

namespace MonotoneCompStatics.QSMChar

/-- p. 164 (remark after Theorem 7): a strictly increasing transformation of a quasisupermodular
function is quasisupermodular. -/
theorem qsm_comp_strictMono {X : Type*} [Lattice X] (f : X → ℝ) (g : ℝ → ℝ)
    (hf : MonotoneCompStatics.Monotonicity.QuasiSupermodularOn f Set.univ) (hg : StrictMono g) :
    MonotoneCompStatics.Monotonicity.QuasiSupermodularOn (g ∘ f) Set.univ := by sorry

end MonotoneCompStatics.QSMChar
