-- Prove2me | Theorems.Thm_NegativeEinsteinFour_nontrivial_fundamental_group
-- name    : NegativeEinsteinFour.nontrivial_fundamental_group
-- status  : Open
-- author  : @xwh
-- created : 2026-10-23T07:55:54.151+00:00
-- url     : https://prove2.me/theorems/0c48b8b1-1b69-4281-93ac-a7f87e2913f9
-- title:
--   Negative Einstein four-manifolds with $b_2=0$ have nontrivial fundamental group
-- statement:
--   Let $M$ be a closed, connected, orientable smooth manifold of real dimension four, and let $g$ be a smooth positive-definite Riemannian metric. Assume that one real constant $\lambda<0$ satisfies $\operatorname{Ric}_g=\lambda g$ everywhere and that $H_2(M;\mathbb R)=0$ (equivalently, $b_2(M)=0$). The conjecture is
--
--   $$\forall p\in M,\qquad\pi_1(M,p)\ne\{1\}.$$
--
--   The conclusion is nontriviality, not infinitude. No sectional-curvature, symmetry, pinching, or collapse hypothesis is imposed, and the carrier is not restricted to the standard smooth four-sphere. The source project explicitly records this target as OPEN / NOT A PROOF.
--
--   **Formalization Note.** The exact declaration and its definition dependencies compiled successfully in Lean 4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474 on 23 October 2026. The theorem body remains the platform-required unproved placeholder. This validates the statement's well-typedness, not the truth of the conjecture. Independent blind read-back and source comparison found the statement faithful to the pinned source target (T).
-- source:
--   https://github.com/liushuijixiang/siwei-einstein/blob/8c02be189f097080feca952347c9104bfb986242/四维Einstein/research/branches/113c_TARGET_THEOREM_LITERATURE_STATUS_2026.md, target (T), §§1–2; https://github.com/liushuijixiang/siwei-einstein/blob/8c02be189f097080feca952347c9104bfb986242/四维Einstein/PROJECT_STATUS.md, 2026-09-04 status.

import Definitions.Def_NegativeEinsteinFour

set_option autoImplicit false

open scoped Manifold ContDiff

namespace NegativeEinsteinFour

/-- Open conjecture: a closed connected orientable smooth four-manifold carrying a
negative Einstein metric and having zero second Betti number has nontrivial fundamental group. -/
theorem nontrivial_fundamental_group
    (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace FourSpace M] [IsManifold I4 ∞ M]
    [CompactSpace M] [ConnectedSpace M]
    (g : SmoothMetric M)
    (h_orientable : Nonempty (FrameOrientation g))
    (h_einstein : IsNegativeEinstein g)
    (h_betti : HasZeroSecondBetti M) :
    ∀ p : M, Nontrivial (FundamentalGroup M p) := by sorry

end NegativeEinsteinFour
