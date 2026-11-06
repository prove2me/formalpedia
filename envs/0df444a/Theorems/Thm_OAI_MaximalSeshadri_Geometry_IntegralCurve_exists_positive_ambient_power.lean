-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_IntegralCurve_exists_positive_ambient_power
-- name    : OAI.MaximalSeshadri.Geometry.IntegralCurve.exists_positive_ambient_power
-- status  : Open
-- author  : @nonlocally
-- created : 2026-11-05T18:47:33.587208+00:00
-- url     : https://prove2.me/theorems/f94dd5e9-7309-460b-b8fc-67d31afcb47a
-- title:
--   An ample bundle has a positive power of positive degree on a curve
-- statement:
--   Let $S$ be a complex projective smooth surface, let $C$ be an integral curve on $S$, and let $L$ be an ample line bundle on $S$. Then there is a positive integer $m$ such that
--
--   $$
--   0<\deg_C(L^{\otimes m}).
--   $$
--
--   Here $\deg_C$ is `curveDegree`, defined as the difference between the Euler characteristic of the pulled-back bundle and that of the structure sheaf of $C$. This supplies the positive-power step used to establish positivity for the original ample bundle.
--
--   **Formalization Note** This statement is verbatim from OpenAI's Lean development, with the supporting development imported through its `Definitions` bundles.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026; Lean declaration `OAI.MaximalSeshadri.Geometry.IntegralCurve.exists_positive_ambient_power`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Sheaves/PullbackSectionOpenExact.lean#L40

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

theorem IntegralCurve.exists_positive_ambient_power (S : Surface) (C : IntegralCurve S)
    (L : LineBundle S.scheme) (hL : L.IsAmple) :
    ∃ m : ℕ, 0 < m ∧ 0 < curveDegree S (L.pow m) C := by
  sorry
