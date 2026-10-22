-- Prove2me | Theorems.Thm_Milne_p1_motive_split
-- name    : Milne.p1_motive_split
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-20T03:11:27.963895+00:00
-- url     : https://prove2.me/theorems/571df5d5-dbfd-447b-bb4c-2c2439d069d5
-- title:
--   The motive of the projective line is the sum of the unit and the Lefschetz motive
-- statement:
--   The motivic decomposition of the projective line (Sections 5-6 of the source): the diagonal of ℙ¹ decomposes as Δ = e₀ + e₂ into orthogonal idempotents, giving h(ℙ¹, Δ) = h(ℙ¹, e₀) ⊕ h(ℙ¹, e₂) — the paper's h(ℙ¹) = 𝟙 ⊕ 𝕃 — and every endomorphism of the motive of the projective line is a rational combination of the two idempotents, the paper's End(h(ℙ¹)) = ℤ ⊕ ℤ.
-- source:
--   J. S. Milne, Motives — Grothendieck's Dream, v2.04, April 2012, Sections 5-6 (p. 7): h(P¹) = 𝟙 ⊕ 𝕃 and End(h(P¹)) = ℤ ⊕ ℤ.

import Mathlib
import Definitions.Def_Milne_world
import Definitions.Def_Milne_motives
import Definitions.Def_Milne_zeta

universe u v

namespace Milne

/-- The motivic decomposition of the projective line (sections 5 and 6 of
the paper): the diagonal of ℙ¹ × ℙ¹ decomposes as Δ = e₀ + e₂ into
orthogonal idempotents, giving h(ℙ¹, Δ) = h(ℙ¹, e₀) ⊕ h(ℙ¹, e₂) — the
paper's h(ℙ¹, Δ) = 𝟙 ⊕ 𝕃 — and every endomorphism of the motive of the
projective line is a ℚ-combination of the two idempotents, the paper's
End(hℙ¹, Δ) = ℤ ⊕ ℤ. -/
theorem p1_motive_split (W : CorrWorld.{u, v}) :
    ∃ i₀ : Hom W (H0 W) (P1M W),
      ∃ i₂ : Hom W (L1 W) (P1M W),
        ∃ p₀ : Hom W (P1M W) (H0 W),
          ∃ p₂ : Hom W (P1M W) (L1 W),
            homComp W i₀ p₀ = idM W (H0 W)
              ∧ homComp W i₂ p₂ = idM W (L1 W)
              ∧ homComp W i₂ p₀ = homZero W (L1 W) (H0 W)
              ∧ homComp W i₀ p₂ = homZero W (H0 W) (L1 W)
              ∧ homAdd W (homComp W p₀ i₀) (homComp W p₂ i₂) = idM W (P1M W)
    ∧ ∀ φ : Hom W (P1M W) (P1M W),
        ∃ a b : ℚ, φ.val = W.add (W.smul a W.e0) (W.smul b W.e2) := by
  sorry

end Milne
