-- Prove2me | Theorems.Thm_OptInapprox_MaxCut_completeness_8_2
-- name    : OptInapprox.MaxCut.completeness_8_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:27:37.073639+00:00
-- url     : https://prove2.me/theorems/8e09fe08-d62a-44e0-8222-71e685bd9ad2
-- title:
--   §8.2 Completeness, p. 19 — honest Long Codes are accepted with probability ≥ (1 − 2η)(1/2 − ρ/2)
-- statement:
--   Let $\mathcal L$ be a Unique Label Cover instance that is regular on the $V$ side, let $-1<\rho<0$, and suppose a labeling satisfies at least a $1-\eta$ fraction of the edges. Encode the label of each $w\in W$ by its Long Code (the dictator of that label). Then the PCP verifier of §8.1 accepts with probability
--   $$\Pr[\mathrm{acc}]\ \ge\ (1-2\eta)\Big(\tfrac12-\tfrac12\rho\Big).$$
--
--   This is the completeness of the reduction from Unique Label Cover to MAX-CUT.
--
--   **Formalization Note.** $V$-regularity is the paper's assumption of §8.1 ("using a result from [38]"); it makes a uniform $v$ and a uniform neighbour a uniform edge.
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), p. 19, §8.2 Completeness

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_Verifier

namespace OptInapprox.MaxCut

theorem completeness_8_2 (L : ULC) (hreg : L.IsVRegular) (ρ : ℝ) (hρ₁ : -1 < ρ) (hρ₂ : ρ < 0)
    (η : ℝ) (lab : (Fin L.nV → Fin L.M) × (Fin L.nW → Fin L.M)) (hlab : 1 - η ≤ L.satFrac lab) :
    (1 - 2 * η) * (1 / 2 - ρ / 2) ≤ accProb L ρ (fun w => longCode (lab.2 w)) := by sorry

end OptInapprox.MaxCut
