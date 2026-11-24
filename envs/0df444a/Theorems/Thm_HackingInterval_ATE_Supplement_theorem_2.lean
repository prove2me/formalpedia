-- Prove2me | Theorems.Thm_HackingInterval_ATE_Supplement_theorem_2
-- name    : HackingInterval.ATE.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T22:56:05.163238+00:00
-- url     : https://prove2.me/theorems/b342ff68-5903-49e8-8ba9-48729909c885
-- title:
--   Theorem 2 (corrected: squared quantile) — both ATE endpoints match the displayed t interval
-- statement:
--   Let $D$ be arbitrary treatment data with $n$ observations, $p$ confounder columns, and binary treatment indicator. Assume the full design $\widetilde X=[X,1[\mathrm{treated}]]$ has invertible Gram matrix and $\nu=n-p-1>0$. Let $0<\alpha<1$ and let $q=Q_\nu(1-\alpha/2)$ be the quantile of the actual Student-t law defined above. Write $s$ for the full-design SSE, $\widetilde\beta_{0,\mathrm{LS}}$ for the treatment least-squares coefficient, and $V_{tt}$ for its inverse-Gram diagonal. Set
--
--   $$\theta=s\left(1+\frac{q^2}{\nu}\right).$$
--
--   Then $q>0$, $F_\nu(q)=1-\alpha/2$, $s\le\theta$, and both endpoints agree:
--
--   $$\left(\beta^*_{0,\min}(\theta),\beta^*_{0,\max}(\theta)\right)=\left(\widetilde\beta_{0,\mathrm{LS}}-q\sqrt{s/\nu}\sqrt{V_{tt}},\widetilde\beta_{0,\mathrm{LS}}+q\sqrt{s/\nu}\sqrt{V_{tt}}\right).$$
--
--   The equality identifies the loss threshold producing the paper's displayed classical ATE interval, including the zero-residual case. Quantile positivity and its CDF characterization are part of the claim, not statistical assumptions. The printed threshold omits the square, while published Appendix D ec17 supplies it.
--
--   Differences from the source:
--   - correction: the printed threshold is SSE(1+q/ν) → the threshold is SSE(1+q²/ν); reason: Appendix D ec17 squares the equality of half-widths; at ν=1, q=2 and SSE=Vtt=1 the printed half-width is √2 rather than 2 (DISPROOF.md)
--   - encoding: the displayed inverses and t interval presuppose full rank and positive residual degrees of freedom → IsUnit of the full Gram determinant, p+1<n, and 0<α<1 are explicit; reason: these exclude singular inverses and undefined t levels or degrees; no valid source interval is removed
--   - encoding: Theorem 2 uses the full-regression residual underlying the standard interval → the immutable published TreatData.SSE is reused; reason: the base mission already corrects the X-only SSE misprint; no base definition is changed
--   - generalization: the comparison is framed under Gaussian linear-model errors → the endpoint equality holds for every observed response vector; reason: matching these deterministic boundary formulas requires no sampling hypothesis and specializes to every Gaussian realization
--   - encoding: q is the upper Student-t quantile → q is the generalized inverse of a normalized Gaussian-ratio law, with positivity and CDF identity asserted as conclusions; reason: this makes the named distribution precise without assuming any needed quantile fact
-- source:
--   Coker, Rudin & King, A Theory of Statistical Inference for Ensuring the Robustness of Scientific Results, Management Science (Articles in Advance, 2021), DOI 10.1287/mnsc.2020.3818, pp. 11–12 (PDF 12–13), Theorem 2, eq. (18); published Online Appendix D ec17

import Mathlib
import Definitions.Def_HackingInterval_ATE_Supplement_Calibration
open Matrix MeasureTheory ProbabilityTheory

namespace HackingInterval.ATE.Supplement

/-- Theorem 2, with the square in θ restored from Appendix D ec17.
The positivity and CDF characterization of the Student-t quantile are conclusions. -/
theorem theorem_2 {n p : ℕ} (D : TreatData n p)
    (hrank : IsUnit (D.Xtᵀ * D.Xt).det) (hdof : p + 1 < n)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    let ν := residualDof n p
    let q := studentQuantile ν (1 - α / 2)
    let θ := calibratedTheta D.SSE ν q
    0 < q ∧ cdf (studentLaw ν) q = 1 - α / 2 ∧
      D.SSE ≤ θ ∧ (D.beta0Min θ, D.beta0Max θ) = ateClassical D ν q := by sorry

end HackingInterval.ATE.Supplement
