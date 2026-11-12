-- Prove2me | Theorems.Thm_GMMPostSamp_Main_lemma_1
-- name    : GMMPostSamp.Main.lemma_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T06:22:24.468306+00:00
-- url     : https://prove2.me/theorems/e138e94a-2710-41b1-854c-120631d620b8
-- title:
--   Lemma 1 — a uniform covariance bound on all tilts is equivalent to a uniform sub-Gaussian log-MGF bound
-- statement:
--   Let $\pi$ be a probability measure on a standard Borel space $\Omega$ and $t:\Omega\to\mathbb R^d$ a measurable statistic with $Z_t(v)=\int e^{\langle v,t\rangle}d\pi<\infty$ for every $v\in\mathbb R^d$. Write $T_{v,t}\pi$ for the exponential tilt. Then, for every $\beta\in\mathbb R$,
--   $$\Big(\mathrm{Cov}_{T_{v,t}\pi}[t]\preceq\beta I_d\ \ \forall v\Big)\iff\Big(\log\mathbb E_{T_{v,t}\pi}\big[e^{\langle u,\,t-\mathbb E_{T_{v,t}\pi}[t]\rangle}\big]\le\tfrac\beta2\|u\|_2^2\ \ \forall u,v\Big).$$
--   Both sides say that $\log Z_t$ is $\beta$-smooth; the right-hand side is the form used in (15).
--
--   **Formalization Note.** The covariance bound is written $\mathrm{Var}[\langle u,t\rangle]\le\beta\|u\|^2$ for every $u$, and the log-MGF bound as $\mathbb E[e^{\langle u,t-\mathbb E t\rangle}]\le e^{\beta\|u\|^2/2}$.
--
--   Differences from the source:
--   - reading: Let π ∈ P(Ω) and t : Ω → R^d (tilts as in (7)) → t measurable and Z_t(v) < ∞ for every v; reason: T_{v,t}π (7) is defined only when Z_t(v) < ∞; Fact 1 and the standing setting of §2.3/§3.2 assume it
--   - encoding: Cov_{T_{v,t}π}[t] ⪯ βI_d → 0 ≤ β‖u‖² and Var_{T_{v,t}π}[⟨u, t⟩] ≤ β‖u‖² for every u (variance in [0, ∞]); reason: the Loewner order is the order of quadratic forms; 0 ≤ β‖u‖² keeps ENNReal.ofReal from clamping a negative bound to 0, so for β < 0 both sides are false as on the page
--   - encoding: log E[exp⟨u, t − E t⟩] ≤ (β/2)‖u‖² → E[exp⟨u, t − E t⟩] ≤ exp((β/2)‖u‖²) as a [0, ∞]-valued integral; reason: log is increasing; the two forms are equivalent
-- source:
--   Kumar, Sarkar, Tian, Zhu, Posterior Sampling in Gaussian Mixture Models Beyond the Clusterability Threshold, STOC 2027 submission (manuscript sha256 ba5079cd…), p. 10, Lemma 1

import Mathlib
import Definitions.Def_GMMPostSamp_Main_Toolkit

open MeasureTheory ProbabilityTheory

namespace GMMPostSamp.Main

/-- Lemma 1 (p. 10): for a probability measure `π` on `Ω` and a statistic `t : Ω → ℝ^d` with
`Z_t(v) < ∞` for every `v`, the covariance bound `Cov_{T_{v,t}π}[t] ⪯ β I_d` for all `v` is
equivalent to the sub-Gaussian log-MGF bound
`log E_{T_{v,t}π}[exp⟨u, t − E_{T_{v,t}π}[t]⟩] ≤ (β/2)‖u‖²` for all `u, v`. -/
theorem lemma_1 {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] {d : ℕ}
    (π : Measure Ω) [IsProbabilityMeasure π] (t : Ω → EuclideanSpace ℝ (Fin d))
    (ht : Measurable t) (hZ : ∀ v, Zt π t v < ⊤) (β : ℝ) :
    (∀ v, CovLe (tilt π t v) t β) ↔ (∀ v, LogMGFLe (tilt π t v) t β) := by sorry

end GMMPostSamp.Main
