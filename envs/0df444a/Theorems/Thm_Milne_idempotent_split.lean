-- Prove2me | Theorems.Thm_Milne_idempotent_split
-- name    : Milne.idempotent_split
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-20T03:10:00.85155+00:00
-- url     : https://prove2.me/theorems/724ee26f-e136-4632-a3b0-f6a25628e70a
-- title:
--   Effective motives are pseudo-abelian: idempotent endomorphisms split
-- statement:
--   An idempotent degree-zero endomorphism f of a motive h(X, e), sandwiched by the projector e (so that e f e = f), decomposes the motive into the direct sum of its complement and image summands h(X, e − f) ⊕ h(X, f), expressed through the five biproduct identities of the two inclusions and two projections (Section 6 of the source: the category of motives is pseudo-abelian).
-- source:
--   J. S. Milne, Motives — Grothendieck's Dream, v2.04, April 2012, Section 6 (p. 7): the category of motives is pseudo-abelian.

import Mathlib
import Definitions.Def_Milne_world
import Definitions.Def_Milne_motives
import Definitions.Def_Milne_zeta

universe u v

namespace Milne

/-- The category of effective motives is pseudo-abelian (section 6 of the
paper): an idempotent f in the endomorphism ring of a motive
M = h(X, e) decomposes the motive into the direct sum of its kernel and
image summands h(X, e − f) ⊕ h(X, f). The direct sum is expressed
through its projection-inclusion equations. -/
theorem idempotent_split (W : CorrWorld.{u, v}) (M : MotElem W) (f : W.Corr M.X M.X)
    (hf : W.cc f f = f) (hdf : W.deg f = 0) (hfe : W.cc (W.cc M.e f) M.e = f) :
    ∃ i₁ : Hom W (idemCompl W M f hf hdf hfe) M,
      ∃ i₂ : Hom W (idemImg W M f hf hdf) M,
        ∃ p₁ : Hom W M (idemCompl W M f hf hdf hfe),
          ∃ p₂ : Hom W M (idemImg W M f hf hdf),
            homComp W i₁ p₁ = idM W (idemCompl W M f hf hdf hfe)
              ∧ homComp W i₂ p₂ = idM W (idemImg W M f hf hdf)
              ∧ homComp W i₂ p₁ =
                homZero W (idemImg W M f hf hdf) (idemCompl W M f hf hdf hfe)
              ∧ homComp W i₁ p₂ =
                homZero W (idemCompl W M f hf hdf hfe) (idemImg W M f hf hdf)
              ∧ homAdd W (homComp W p₁ i₁) (homComp W p₂ i₂) = idM W M := by
  sorry

end Milne
