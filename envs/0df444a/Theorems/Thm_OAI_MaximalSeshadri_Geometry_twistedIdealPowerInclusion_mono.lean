-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_twistedIdealPowerInclusion_mono
-- name    : OAI.MaximalSeshadri.Geometry.twistedIdealPowerInclusion_mono
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T15:18:24.608295+00:00
-- url     : https://prove2.me/theorems/e5296473-e164-4bc7-a49f-569d7878a59c
-- title:
--   Twisted ideal power inclusions are monomorphisms
-- statement:
--   For line bundles $L,J$ on a scheme, a monomorphism $\iota:J\to\mathcal O_X$, and $a,b,n$: the map $(L^a\otimes J^b)^n\to L^{an}$ (`twistedIdealPowerInclusion`) is a monomorphism.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.twistedIdealPowerInclusion_mono`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/LocalAlgebra/TwistedIdealPower.lean#L32

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames

variable {X : Scheme.{0}}

theorem twistedIdealPowerInclusion_mono (L J : LineBundle X) (ι : J.sheaf ⟶ O X)
    [Mono ι] (a b n : ℕ) : Mono (twistedIdealPowerInclusion L J ι a b n) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
