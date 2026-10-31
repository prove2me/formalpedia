-- Prove2me | Theorems.Thm_FrechetPrefs_penalty_identity
-- name    : FrechetPrefs.penalty_identity
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:04:10.696983+00:00
-- url     : https://prove2.me/theorems/83df44fc-479e-4e95-b3b3-1768d13204f6
-- title:
--   Proof of Theorem 2, p.ec6 — the penalty identity
-- statement:
--   Let $Q_1,\dots,Q_n\in P_2(\mathbb R)$, $w\in\Delta^{n-1}$, $Q_B$ a barycenter, and $Q\in P_2(\mathbb R)$ with quantile $F^{-1}$. Then
--   $$F_{\mathbb M}(Q)-F_{\mathbb M}(Q_B)=\int_0^1\big(F^{-1}(s)-F_B^{-1}(s)\big)^2\,ds.$$
--
--   This is the "simple algebraic manipulation of the penalty term" behind (7): the penalty in (4) is the squared distance to the barycenter.
--
--   Differences from the source:
--   - encoding: quantile functions on [0,1] → quantiles evaluated on the open interval (0,1); reason: the endpoints are null, and F⁻¹(1) can be infinite; no integral changes
-- source:
--   Petracou, Xepapadeas, Yannacopoulos, Decision Making under Model Uncertainty: Fréchet-Wasserstein Mean Preferences, manuscript MS-DEC-19-01009-REV (accepted manuscript, hdl.handle.net/11585/863779), proof of Theorem 2, p.ec6

import Mathlib
import Definitions.Def_FrechetPrefs_InadaUtility
import Definitions.Def_FrechetPrefs_Multiplier

open MeasureTheory Set Filter Topology

namespace FrechetPrefs

/-- Proof of Theorem 2, p.ec6 of manuscript MS-DEC-19-01009-REV: the algebraic manipulation of the
penalty term in (7), `F_M(Q) − F_M(Q_B) = ∫₀¹ (F⁻¹(s) − F_B⁻¹(s))² ds`.

**Formalization Note.** The display for `F_M(g + εh)` on p.ec3 omits the second-order term and is
not the source of this identity. -/
theorem penalty_identity {n : ℕ} (w : Fin n → ℝ) (Q : Fin n → ProbabilityMeasure ℝ)
    (B μ : ProbabilityMeasure ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hQ : ∀ i, Q i ∈ P2)
    (hB : IsBarycenter w Q B) (hμ : μ ∈ P2) :
    frechet w Q μ - frechet w Q B = ∫ s in Ioo (0 : ℝ) 1, (q μ s - q B s) ^ 2 := by sorry

end FrechetPrefs
