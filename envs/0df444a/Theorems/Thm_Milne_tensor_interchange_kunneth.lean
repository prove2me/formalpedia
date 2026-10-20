-- Prove2me | Theorems.Thm_Milne_tensor_interchange_kunneth
-- name    : Milne.tensor_interchange_kunneth
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-20T03:10:46.40986+00:00
-- url     : https://prove2.me/theorems/da1d6141-62d6-4de5-b087-fad1d9a67ec5
-- title:
--   The tensor product of motives and the Künneth formula
-- statement:
--   The tensor structure of Section 6 of the source: the exterior product of morphisms composes componentwise (the interchange law), the exterior product of the identities of two motives is the identity of their tensor product, and the Künneth formula holds for the functor X ↦ hX: hX ⊗ hY = h(X × Y).
-- source:
--   J. S. Milne, Motives — Grothendieck's Dream, v2.04, April 2012, Section 6 (p. 7): the tensor structure and the Künneth formula.

import Mathlib
import Definitions.Def_Milne_world
import Definitions.Def_Milne_motives
import Definitions.Def_Milne_zeta

universe u v

namespace Milne

/-- The tensor structure and the Künneth formula (section 6 of the
paper): the exterior product of morphisms composes componentwise, the
exterior product of identities is the identity of the tensor product, and
the Künneth formula holds for the functor X ↦ hX:
hX ⊗ hY = h(X × Y). -/
theorem tensor_interchange_kunneth (W : CorrWorld.{u, v}) (X Y : W.Var)
    (M M' N N' P P' : MotElem W)
    (f : Hom W M N) (g : Hom W N P) (f' : Hom W M' N') (g' : Hom W N' P') :
    crossHom W (homComp W f g) (homComp W f' g') =
      homComp W (crossHom W f f') (crossHom W g g')
      ∧ crossHom W (idM W M) (idM W N) = idM W (tensorObj W M N)
      ∧ tensorObj W (hOf W X) (hOf W Y) = hOf W (W.prod X Y) := by
  sorry

end Milne
