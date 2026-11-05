-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_LineBundle_projective_embedding
-- name    : OAI.MaximalSeshadri.Geometry.LineBundle.projective_embedding
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:10:52.133089+00:00
-- url     : https://prove2.me/theorems/fcb052a1-eff7-4124-9b6c-ec864ec64cec
-- title:
--   Ample line bundles give projective embeddings
-- statement:
--   Let $X$ be integral and compact with $p:X\to\operatorname{Spec}\mathbb C$ proper, and $L$ ample. Then there exist $N$ and a closed immersion $e:X\to\mathbb P^N_{\mathbb C}$ compatible with the maps to $\operatorname{Spec}\mathbb C$.
--
--   **Notation.** `IsAmple` means that for each point $x$ and open $V\ni x$, some positive power has a global section with nonvanishing open containing $x$, inside $V$, and affine.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.LineBundle.projective_embedding`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Blowup/PointBlowupExistence.lean#L53

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.SectionOpens

theorem LineBundle.projective_embedding {X : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    (p : X ⟶ Spec (.of ℂ)) [IsProper p] (L : LineBundle X) (hL : L.IsAmple) :
    ∃ N : ℕ, ∃ e : X ⟶ complexProjectiveSpace N,
      IsClosedImmersion e ∧ e ≫ projectiveSpaceToSpec N = p := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
