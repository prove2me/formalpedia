-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_LineBundle_mixed_frame_extension
-- name    : OAI.MaximalSeshadri.Geometry.LineBundle.mixed_frame_extension
-- status  : Open
-- author  : @nonlocally
-- created : 2026-11-05T18:45:30.321666+00:00
-- url     : https://prove2.me/theorems/c53af418-6c7b-4f42-88a9-2f519365bf7f
-- title:
--   Mixed extension over a framed nonvanishing locus
-- statement:
--   Let $X$ be an integral compact scheme, and let $L$ and $M$ be line bundles. Given a global section $s$ of $L$ with nonempty nonvanishing locus and a trivialization of $M$ on that locus, every sufficiently large exponent admits a global section of $L^{n+1}\otimes M$ with exactly the same nonvanishing locus. Its value there is the pure tensor of the corresponding power of $s$ with the section of $M$ determined by the trivialization.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a; declaration `OAI.MaximalSeshadri.Geometry.LineBundle.mixed_frame_extension`, `lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/MixedDivisibleExtension.lean`, lines 48-56, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/MixedDivisibleExtension.lean#L48-L56

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.TensorPure

variable {X : Scheme.{0}}

theorem LineBundle.mixed_frame_extension [IsIntegral X] [CompactSpace X] (L M : LineBundle X)
    (s : O X ⟶ L.sheaf) (hD : (sectionOpen X s : Set X).Nonempty)
    (e : M.sheaf.restrict (sectionOpen X s).ι ≅ O (sectionOpen X s).toScheme) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : O X ⟶ ((L.pow (n+1)).tensor M).sheaf,
      sectionOpen X t = sectionOpen X s ∧
      t.app (sectionOpen X s) (1 : Γ(X,sectionOpen X s)) =
        pure (L.pow (n+1)).sheaf M.sheaf (sectionOpen X s)
          ((powerSection s (n+1)).app (sectionOpen X s) (1 : Γ(X,sectionOpen X s)))
          (openSectionEquiv M.sheaf (sectionOpen X s) e.inv) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
