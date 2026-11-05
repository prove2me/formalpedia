-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_IsBlowup_eventual_ample_power_twist
-- name    : OAI.MaximalSeshadri.Geometry.IsBlowup.eventual_ample_power_twist
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:04:39.354316+00:00
-- url     : https://prove2.me/theorems/7cadfc6e-ec0b-44e0-abae-6296513ab765
-- title:
--   Ample twists of the pulled-back bundle on a blow-up
-- statement:
--   Let $f:Y\to X$ be a blow-up of an ideal sheaf $I$ with $Y$ integral and $X,Y$ compact, $L$ ample on $X$, and $J,\iota$ presenting the pullback of $I$. Then there are $a>0$ and $N$ such that for all $n\ge N$ the bundle $(f^*L)^{a(n+1)}\otimes J$ is ample on $Y$.
--
--   **Notation.** `PresentsPullbackIdeal I f J ι` says that $\iota:J\to\mathcal O_Y$ is a monomorphism whose image on affine opens is the extension of $I$ along $f$. `IsBlowup I π` says that $I$ pulls back to an invertible ideal along $\pi$ and that $\pi$ is universal with this property. `IsAmple` means that for each point $x$ and open $V\ni x$, some positive power has a global section with nonvanishing open containing $x$, inside $V$, and affine.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.IsBlowup.eventual_ample_power_twist`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Blowup/BlowupIntersection.lean#L28

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.NefNumerics

theorem IsBlowup.eventual_ample_power_twist {X Y : Scheme.{0}} [IsIntegral Y]
    [CompactSpace Y] [CompactSpace X] {I : X.IdealSheafData} {f : Y ⟶ X}
    (hb : IsBlowup I f) (L : LineBundle X) (hL : L.IsAmple)
    (J : LineBundle Y) (ι : J.sheaf ⟶ O Y) (hJ : PresentsPullbackIdeal I f J ι) :
    ∃ a N : ℕ, 0 < a ∧ ∀ n : ℕ, N ≤ n →
      (((L.pullback f).pow (a*(n+1))).tensor J).IsAmple := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
