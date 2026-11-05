-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_LineBundle_divisible_mixed_extension
-- name    : OAI.MaximalSeshadri.Geometry.LineBundle.divisible_mixed_extension
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:05:24.487952+00:00
-- url     : https://prove2.me/theorems/0a7075db-0880-469c-98d7-35a07c36b6fc
-- title:
--   Extension of sections after a power twist, in divisible form
-- statement:
--   Let $X$ be integral and compact, $L,M$ line bundles, $s$ a section of $L$ with nonempty nonvanishing open $D$, and $w$ a section of $M$ over $D$. Then there is $N$ such that for all $n\ge N$ there is a global section $t$ of $L^{n+1}\otimes M$ with nonvanishing open contained in $D$ which restricts on $D$ to $s^{n+1}\otimes w$.
--
--   **Notation.** `sectionOpen X s` is the same union for a global section $s$: its nonvanishing open.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.LineBundle.divisible_mixed_extension`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/MixedDivisibleExtension.lean#L23

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Frames MaximalSeshadri.TensorPure

variable {X : Scheme.{0}}

theorem LineBundle.divisible_mixed_extension [IsIntegral X] [CompactSpace X] (L M : LineBundle X)
    (s : O X ⟶ L.sheaf) (hD : (sectionOpen X s : Set X).Nonempty)
    (w : Γ(M.sheaf,sectionOpen X s)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : O X ⟶ ((L.pow (n+1)).tensor M).sheaf,
      sectionOpen X t ≤ sectionOpen X s ∧
      t.app (sectionOpen X s) (1 : Γ(X,sectionOpen X s)) =
        pure (L.pow (n+1)).sheaf M.sheaf (sectionOpen X s)
          ((powerSection s (n+1)).app (sectionOpen X s) (1 : Γ(X,sectionOpen X s))) w := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
