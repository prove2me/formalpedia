-- Prove2me | Theorems.Thm_OAI_PiExponent_determinant_bounds_inconsistent
-- name    : OAI.PiExponent.determinant_bounds_inconsistent
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-09T14:19:07.540533+00:00
-- url     : https://prove2.me/theorems/a9904f48-a524-4023-b106-063256a5e681
-- title:
--   Incompatible determinant bounds
-- statement:
--   For real numbers \(\nu,\theta,x,b,e_{\rm ar},e_{\rm an},e_{\rm r},c,d\), the following hypotheses are inconsistent:
--
--   $$\begin{aligned}
--   1&<\nu,\qquad 0\le b\le\theta,\\
--   e_{\rm ar}+e_{\rm an}+e_{\rm r}&<\nu(x-\theta)-(1-\theta),\\
--   1+e_{\rm ar}+e_{\rm an}+e_{\rm r}&<c,\\
--   -(1-b)-e_{\rm ar}&\le d\le e_{\rm an}+e_{\rm r}+\max\{-c,-\nu(x-b)\}.
--   \end{aligned}$$
--
--   The result isolates the contradiction between a lower determinant estimate and the competing analytic/collision upper estimate.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/Comparison.lean#L10-L26

import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.Real.Lemmas

namespace OAI
namespace PiExponent
open Filter Topology

theorem determinant_bounds_inconsistent
    (nu theta x b ear ean err collision d : ℝ)
    (hnu : 1 < nu) (hb0 : 0 ≤ b) (hb : b ≤ theta)
    (hgap : ear + ean + err < nu * (x - theta) - (1 - theta))
    (hcollision : 1 + ear + ean + err < collision)
    (hlower : -(1 - b) - ear ≤ d)
    (hupper : d ≤ ean + err + max (-collision) (-nu * (x - b))) : False := by
  sorry

end PiExponent
end OAI
