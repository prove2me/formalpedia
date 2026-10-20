-- Prove2me | Theorems.Thm_Milne_mot_category_axioms
-- name    : Milne.mot_category_axioms
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-20T03:09:24.59847+00:00
-- url     : https://prove2.me/theorems/e3898ea9-a735-45c6-af1d-fcc94aee7008
-- title:
--   Effective motives form a category
-- statement:
--   The category axioms for the category of effective pure motives (Section 5 of the source: "Correspondences compose, and so this is a category"): composition of morphisms — sandwich-fixed degree-zero correspondences — is associative, and the idempotent correspondence of a motive is a two-sided identity for composition.
-- source:
--   J. S. Milne, Motives — Grothendieck's Dream, v2.04, April 2012, Section 5 (p. 6): correspondences compose, and so this is a category.

import Mathlib
import Definitions.Def_Milne_world
import Definitions.Def_Milne_motives
import Definitions.Def_Milne_zeta

universe u v

namespace Milne

/-- The category axioms for the category of effective motives (section 5
of the paper: "Correspondences compose, and so this is a category"):
composition of morphisms is associative, and the idempotent correspondence
of a motive is a two-sided identity for composition. -/
theorem mot_category_axioms (W : CorrWorld.{u, v}) (M N P Q : MotElem W)
    (f : Hom W M N) (g : Hom W N P) (h : Hom W P Q) :
    homComp W (homComp W f g) h = homComp W f (homComp W g h)
      ∧ homComp W (idM W M) f = f
      ∧ homComp W f (idM W N) = f := by
  sorry

end Milne
