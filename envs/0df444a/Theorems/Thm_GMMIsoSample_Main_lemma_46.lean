-- Prove2me | Theorems.Thm_GMMIsoSample_Main_lemma_46
-- name    : GMMIsoSample.Main.lemma_46
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:33:43.427431+00:00
-- url     : https://prove2.me/theorems/be71ee6c-299d-4ffe-bf96-05056b253a5d
-- title:
--   Lemma 46 — d_TV(Q_r^(T), Q_s^(T)) ≤ T(s² − r²)/(2√(2d))
-- statement:
--   Let $d\ge1$. For $r\ge0$ and $T\ge1$, $Q_r^{(T)}$ is the law of $(X_1,\dots,X_T)$ where $U\sim\mathrm{Unif}(S^{d-1})$, $\theta=rU$, and $X_1,\dots,X_T$ are i.i.d. $N(\theta,I_d)$ given $U$. For every $T\ge1$ and $0\le r\le s$,
--   $$d_{TV}\big(Q_r^{(T)},Q_s^{(T)}\big)\le\frac{T(s^2-r^2)}{2\sqrt{2d}}.$$
--
--   It bounds the prior-averaged sample laws in Propositions 54 and 57.
--
--   Differences from the source:
--
--   - encoding: Unif(S^{d−1}) → the law of g/‖g‖ for g ∼ N(0, I_d); reason: this is the rotation-invariant probability on the sphere
--   - encoding: ℝ^d with d ≥ 1 implicit (S^{d−1}) → hypothesis 1 ≤ d; reason: the sphere S^{d−1} and the paper's dimension require d ≥ 1
-- source:
--   Chen, De, Lee, Servedio, Sublinear Sample Size Suffices for Learning Mixtures of Gaussians up to Isometry, STOC 2027 submission (version of November 3, 2026, sha256 411f3581…), p. 64, Lemma 46

import Mathlib
import Definitions.Def_PolySampIso_Divergences
import Definitions.Def_GMMIsoSample_Main_Model
import Definitions.Def_GMMIsoSample_Main_LowerBound

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GMMIsoSample.Main

/-- Lemma 46 (p. 64): in `ℝ^d` (`d ≥ 1`), for every `T ≥ 1` and `0 ≤ r ≤ s`,
`d_TV(Q_r^(T), Q_s^(T)) ≤ T(s² − r²)/(2√(2d))`. -/
theorem lemma_46 (d T : ℕ) (r s : ℝ) (hd : 1 ≤ d) (hT : 1 ≤ T) (hr : 0 ≤ r) (hrs : r ≤ s) :
    PolySampIso.tvDist (sphereSampleLaw d T r) (sphereSampleLaw d T s) ≤
      T * (s ^ 2 - r ^ 2) / (2 * Real.sqrt (2 * d)) := by sorry

end GMMIsoSample.Main
