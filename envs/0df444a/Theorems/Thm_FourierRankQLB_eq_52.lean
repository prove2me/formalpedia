-- Prove2me | Theorems.Thm_FourierRankQLB_eq_52
-- name    : FourierRankQLB.eq_52
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:46:03.027411+00:00
-- url     : https://prove2.me/theorems/ee098b58-ea6c-430d-a2e1-104af642aeb3
-- title:
--   Eq. (52) — the optimal value of a padded objective
-- statement:
--   Let $n\ge2$, $d=d_n$, $s>0$ and $Q\in O(d)$. For a unit vector $v\in\mathbb R^d$ with padding $\overline v=(v,0_{\ell_n})$,
--   $$
--   h_{K_{s,Q}}(\overline v)=s\sqrt{v^TA_Q^{-1}v},\qquad Z(Q,v)=\frac{\sqrt{a_dd}}{s}\,h_{K_{s,Q}}(\overline v).
--   $$
--
--   Thus an estimate of the optimal value with additive error $s/(200\sqrt{a_dd})$ is an estimate of $Z(Q,v)$ with additive error $1/200$, which is how an optimizer becomes a determinant predictor.
--
--   Differences from the source:
--
--   - encoding: the ambient dimension $n$ of §4–5, with §5.1 fixing $n\ge2$ → hypothesis `2 ≤ n`; reason: the standing assumption; it excludes $d=0$, where $g_d$ and the radii degenerate
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Eq. (52), p.31

import Mathlib
import Definitions.Def_FourierRankQLB_hardBody
import Definitions.Def_FourierRankQLB_supportFn
import Definitions.Def_FourierRankQLB_padObj
import Definitions.Def_FourierRankQLB_Zstat

open Matrix

namespace FourierRankQLB

/-- Eq. (52): for a unit vector `v`, `h_{K_{s,Q}}(v̄) = s √(vᵀA_Q⁻¹v)` and
`Z(Q, v) = (√(a_d d)/s) h_{K_{s,Q}}(v̄)`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Eq. (52), p. 31. -/
theorem eq_52 {n : ℕ} (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) (Q : Od (dn n)) (v : Fin (dn n) → ℝ)
    (hv : v ⬝ᵥ v = 1) :
    supportFn (hardBody s Q) (padObj v) = s * √(v ⬝ᵥ ((AQ Q)⁻¹ *ᵥ v)) ∧
      Zstat Q v = √(ad (dn n) * dn n) / s * supportFn (hardBody s Q) (padObj v) := by sorry

end FourierRankQLB
