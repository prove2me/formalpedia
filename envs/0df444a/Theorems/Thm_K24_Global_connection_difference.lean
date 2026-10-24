-- Prove2me | Theorems.Thm_K24_Global_connection_difference
-- name    : K24.Global.connection_difference
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-23T18:32:38.417574+00:00
-- url     : https://prove2.me/theorems/f61a8f7c-668e-424e-867f-adf9699a0320
-- title:
--   K24 exact connection difference for C1 metric sections
-- statement:
--   On an arbitrary smooth real four-manifold, let ghat and z be genuine positive symmetric covariant 2-tensor fields whose coordinate coefficients are C1 on every canonical chart target. Then at every chart-target point their actual Christoffel-symbol difference equals one half of the inverse ghat metric contracted with the three z-covariant derivatives of ghat-z, exactly as defined by connectionDifferenceExpansion. This is the connection_formula component of the exact K24 change-of-slice identities. The proof requires no Einstein, compactness or circle-action hypothesis. It supplies the coordinate identity needed before the Bianchi expansion and uniform defect estimates. Applying it to original Holder admissibility still requires proving cover-to-canonical C1 regularity; original Sobolev admissibility already supplies C2 representatives.
-- source:
--   Child dependency of original theorem aac3db7a-b1fb-4137-ab8b-8f9efc4d3b22, ExactChangeOfSliceConclusions.connection_formula. Source K24 section 3.1, Git commit 8c02be189f097080feca952347c9104bfb986242. Original full target and definitions preserved without changes.

import Definitions.Def_K24GlobalStatement
set_option autoImplicit false
open scoped Manifold ContDiff

namespace K24.Global
universe u
theorem connection_difference :
    ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M]
      [IsManifold I4 ∞ M],
      ∀ (ghat z : RawCov2 M), IsMetric ghat → IsMetric z →
        Cov2ContDiff 1 ghat → Cov2ContDiff 1 z →
        ∀ (c : M) (x : FourSpace), x ∈ (chartAt FourSpace c).target →
          ∀ k i j : Fin 4, connectionDifferenceInChart ghat z c x k i j =
            connectionDifferenceExpansion ghat z c x k i j := by
  sorry
end K24.Global
