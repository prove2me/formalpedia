-- Prove2me | Theorems.Thm_Milne_motives_not_tannakian
-- name    : Milne.motives_not_tannakian
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-20T03:13:39.424989+00:00
-- url     : https://prove2.me/theorems/f1a16ea7-dcba-41de-8596-7b24731ff3f8
-- title:
--   The category of effective motives admits no fiber functor
-- statement:
--   The tannakian obstruction (Section 6, page 10 of the source): for a world containing a curve of genus at least 2, the category of effective motives admits no fiber functor — no assignment of finite-dimensional Q-vector spaces to motives that acts on morphisms, preserves identities and composition, multiplies dimensions over tensor products, and identifies the trace of the identity endomorphism of each motive with the dimension of its fiber. Under such an assignment the trace of the identity would be a nonnegative dimension, but the trace of the identity of the motive of a curve of genus g is 2 − 2g, which is negative.
-- source:
--   J. S. Milne, Motives — Grothendieck's Dream, v2.04, April 2012, Section 6 (p. 10): the category of motives is not tannakian.

import Mathlib
import Definitions.Def_Milne_world
import Definitions.Def_Milne_motives
import Definitions.Def_Milne_zeta

universe u v

namespace Milne

/-- The tannakian obstruction (section 6 of the paper, page 10): the
category of effective motives admits no fiber functor — there is no
assignment of finite-dimensional ℚ-vector spaces to motives that acts on
morphisms, preserves identities and composition, multiplies dimensions
over tensor products, and identifies the trace of the identity with the
dimension of the fiber. The reason is the paper's: under such an
assignment the trace of the identity is a nonnegative dimension, but for
a curve of genus g ≥ 2 the trace of the identity of its motive is
2 − 2g, which is negative. -/
theorem motives_not_tannakian (W : CorrWorld.{u, v}) (g : ℕ) (hg : 2 ≤ g) :
    ¬ ∃ F : FibFun W, True := by
  sorry

end Milne
