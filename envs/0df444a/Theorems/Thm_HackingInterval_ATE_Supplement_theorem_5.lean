-- Prove2me | Theorems.Thm_HackingInterval_ATE_Supplement_theorem_5
-- name    : HackingInterval.ATE.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T22:57:30.509884+00:00
-- url     : https://prove2.me/theorems/1c6fb17e-efec-4b7b-88be-3272cabd57be
-- title:
--   Theorem 5 (corrected: scalar prediction center) — both extrema match the displayed t interval
-- statement:
--   Let $D=(X,Y)$ be an arbitrary real least-squares design with $n$ rows and $p$ columns. Assume $X^\top X$ is invertible and $\nu=n-p-1>0$, using exactly the degrees of freedom printed in Theorem 5. Let $x\in\mathbb R^p$ be any prediction covariate, including zero, and let $0<\alpha<1$. Put $q=Q_\nu(1-\alpha/2)$, $s=\mathrm{SSE}$, and
--
--   $$\theta=s\left(1+\frac{q^2}{\nu}\right).$$
--
--   Then $q>0$, $F_\nu(q)=1-\alpha/2$, and $s\le\theta$. The published coefficient vectors $\beta_-^*(\theta,x)$ and $\beta_+^*(\theta,x)$ attain the minimum and maximum of $x^\top\beta$ subject to loss at most $\theta$. Their scalar predictions are exactly
--
--   $$\left(x^\top\beta_-^*,x^\top\beta_+^*\right)=\left(x^\top\beta_{\mathrm{LS}}-q\sqrt{s/\nu}\sqrt{x^\top(X^\top X)^{-1}x},\ x^\top\beta_{\mathrm{LS}}+q\sqrt{s/\nu}\sqrt{x^\top(X^\top X)^{-1}x}\right).$$
--
--   This matches both scalar extrema to the source's displayed comparison pair. It includes zero residuals and the degenerate zero prediction vector, without asserting uniqueness at that vector. It asserts equality with the displayed interval, not a separate nominal-coverage theorem for a p-column no-intercept model, and not an interval for a future noisy response. Published Appendix D ec19 supplies the scalar center missing from the main-text display.
--
--   Differences from the source:
--   - correction: the displayed center is the vector βLS → the center is the scalar xᵀβLS; reason: the theorem names xᵀβ as its target and Appendix D ec19 uses this scalar center; for p=1, βLS=3 and x=2 the centers are 3 and 6 (DISPROOF.md)
--   - encoding: the source prints ν=n−p−1 even for its generic p-column design → the same ν is retained and the claim is equality with that displayed pair; reason: the statement does not silently change the degrees or append a nominal-coverage claim
--   - encoding: the inverse and t quantile presuppose full rank, ν>0 and an interior probability level → IsUnit of the Gram determinant, p+1<n and 0<α<1 are explicit; reason: singular inverses and undefined degrees or quantile levels are excluded; no positive-SSE or nonzero-x premise is imposed
--   - generalization: the comparison is framed under Gaussian linear-model errors → the endpoint and optimality statements hold for every observed Y and every x including zero; reason: the deterministic identities specialize to every source realization; at x=0 all feasible coefficients have the same scalar prediction
--   - encoding: q is the upper Student-t quantile → the actual Gaussian-ratio Student-t law defines q, and positivity and CDF identity are conclusions; reason: no sign, normality of a fitted statistic, or quantile law is assumed to bypass the statistical definition
-- source:
--   Coker, Rudin & King, A Theory of Statistical Inference for Ensuring the Robustness of Scientific Results, Management Science (Articles in Advance, 2021), DOI 10.1287/mnsc.2020.3818, p. 14 (PDF 15), Theorem 5; published Online Appendix D ec19

import Mathlib
import Definitions.Def_HackingInterval_ATE_Supplement_Calibration
open Matrix MeasureTheory ProbabilityTheory

namespace HackingInterval.ATE.Supplement

/-- Theorem 5: both scalar prediction extrema and the displayed t-interval agree.
The center is corrected from the vector βLS to xnewᵀβLS (Appendix D ec19).
The source's ν = n - p - 1 is retained. Zero xnew and zero SSE are included. -/
theorem theorem_5 {n p : ℕ} (D : Design (Fin n) (Fin p))
    (hrank : IsUnit (D.Xᵀ * D.X).det) (hdof : p + 1 < n)
    (xnew : Fin p → ℝ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    let ν := residualDof n p
    let q := studentQuantile ν (1 - α / 2)
    let θ := calibratedTheta D.SSE ν q
    0 < q ∧ cdf (studentLaw ν) q = 1 - α / 2 ∧ D.SSE ≤ θ ∧
      D.IsMinSol θ xnew (D.betaMinus θ xnew) ∧
      D.IsMaxSol θ xnew (D.betaPlus θ xnew) ∧
      (xnew ⬝ᵥ D.betaMinus θ xnew, xnew ⬝ᵥ D.betaPlus θ xnew) =
        predictionClassical D xnew ν q := by sorry

end HackingInterval.ATE.Supplement
