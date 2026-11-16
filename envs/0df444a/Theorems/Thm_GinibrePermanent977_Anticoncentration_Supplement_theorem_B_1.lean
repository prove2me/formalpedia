-- Prove2me | Theorems.Thm_GinibrePermanent977_Anticoncentration_Supplement_theorem_B_1
-- name    : GinibrePermanent977.Anticoncentration.Supplement.theorem_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:38:31.739172+00:00
-- url     : https://prove2.me/theorems/647e395a-3f21-41b0-976f-49877f0c8233
-- title:
--   Theorem B.1 — Study–Cayley determinant comparison
-- statement:
--   Let $G_n^{\mathbb H}$ be a standard quaternionic Ginibre matrix, whose real coordinates have variance $1/4$. Let $\operatorname{Sdet}$ be the Study determinant and
--   $$\operatorname{Cdet}A=\sum_{\sigma\in S_n}\operatorname{sgn}(\sigma)a_{1,\sigma(1)}\cdots a_{n,\sigma(n)},$$
--   with factors in increasing row order. For every $n\ge1$,
--   $$\operatorname{Sdet}(G_n^{\mathbb H})^2\le_{\mathrm{Lt}}|\operatorname{Cdet}(G_n^{\mathbb H})|^2.$$
--   Equivalently, the Laplace expectation of the squared Study determinant is at least that of the squared Cayley magnitude for every nonnegative test parameter. This compares two different quaternionic determinants in distributional order, without asserting pointwise domination or equality of their laws.
--
--   Differences from the source:
--
--   - encoding: Laplace comparison for s ≥ 0 → published LaplaceOrder for s > 0; reason: at s = 0 both bounded integrands equal 1 under probability laws
--   - encoding: the signed row-ordered quaternionic Cayley determinant → the published generic cdetK specialized to Scalar.quaternion; reason: its Leibniz sum needs only a ring and is precisely the Appendix B definition, despite the older base prose describing only its commutative uses
-- source:
--   Frederic Koehler, Pui Kuen Leung, STOC 2027 submission #977 (October 2026), Theorem B.1, p.17 (PDF SHA256 e25737f1d5e3492905f8eeaa41d92c55d95f73622a3b5846cc87aac6a346d4ec)

import Mathlib
import Definitions.Def_GinibrePermanent977_Anticoncentration_Model
open MeasureTheory ProbabilityTheory
open scoped Quaternion

namespace GinibrePermanent977.Anticoncentration.Supplement

/-- Theorem B.1, p.17. Sdet(G)^2 ≤Lt |Cdet(G)|^2; Cayley factors are row-ordered. -/
theorem theorem_B_1 (n : ℕ) (hn : 1 ≤ n) :
    StochasticOrders.LaplaceTransform.LaplaceOrder
      (ginibre .quaternion n n) (ginibre .quaternion n n)
      (fun G => studyDet G ^ 2) (fun G => ‖cdetK G‖ ^ 2) := by sorry

end GinibrePermanent977.Anticoncentration.Supplement
