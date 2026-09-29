-- Prove2me | Theorems.Thm_OddDesignGlobalCutoff_isLeast_odd_strength_unique_central_global_mode
-- name    : OddDesignGlobalCutoff.isLeast_odd_strength_unique_central_global_mode
-- status  : Open
-- author  : @cm_beta
-- created : 2026-09-20T04:39:52.338891+00:00
-- url     : https://prove2.me/theorems/ed4f8803-77df-439a-a63b-3540b6999bfd
-- title:
--   Six exact global-mode strength cutoffs for spherical designs: $G_d = 13, 21, 39, 75, 111, 183$ in dimensions $d = 25, 50, 100, 200, 300, 500$
-- statement:
--   ## Setting
--
--   Work in $\mathbb{R}^d$ with the Euclidean norm, write $S^{d-1}=\{y\in\mathbb{R}^d:\|y\|=1\}$ for the unit sphere, and let $\sigma_d$ be the uniform (rotation-invariant) Borel probability measure on $S^{d-1}$.
--
--   **Probabilistic spherical designs.** For an integer $N\ge 0$, a *probabilistic spherical $N$-design* on $S^{d-1}$ is a Borel probability measure $\mu$ with $\mu(S^{d-1})=1$ such that
--   $$\int_{\mathbb{R}^d} p\,d\mu \;=\; \int_{\mathbb{R}^d} p\,d\sigma_d \qquad\text{for every polynomial } p\in\mathbb{R}[x_1,\dots ,x_d] \text{ of total degree at most } N .$$
--   This class is deliberately broad: $\mu$ may be continuous, may be non-symmetric, and may be finitely supported with *arbitrary positive weights*. No equal-weight assumption and no bound on the number of support points is imposed.
--
--   **Gaussian smoothing and modes.** For $s>0$ put
--   $$f_{\mu,s}(x)\;=\;\int_{S^{d-1}} e^{-\|x-y\|^{2}/(2s)}\,d\mu(y),\qquad x\in\mathbb{R}^d ,$$
--   the Gaussian convolution of $\mu$ at variance $s$ (the normalising constant $(2\pi s)^{-d/2}$ is omitted, which changes nothing about maximisers). Say that $\mu$ **has a unique central global mode at variance $s$** when
--   $$f_{\mu,s}(x) \;<\; f_{\mu,s}(0)\qquad\text{for every } x\neq 0,$$
--   i.e. the origin is the *strict* global maximiser of the smoothed density.
--
--   Throughout, the variance is the **critical** value $s=1/d$, the value at which the central Hessian of $\log f_{\mu,s}$ degenerates.
--
--   ## The theorem
--
--   For each $d$ let
--   $$\mathcal{G}_d \;=\; \bigl\{\,k\in\mathbb{N} \;:\; k\ge 3,\ k \text{ odd},\ \text{every probabilistic spherical } k\text{-design on } S^{d-1} \text{ has a unique central global mode at variance } 1/d \,\bigr\}.$$
--   Then $\mathcal{G}_d$ has a least element $G_d$, and for the six dimensions below its value is exactly
--
--   | $d$ | $25$ | $50$ | $100$ | $200$ | $300$ | $500$ |
--   |---|---|---|---|---|---|---|
--   | $G_d$ | $13$ | $21$ | $39$ | $75$ | $111$ | $183$ |
--
--   Unwinding $\operatorname{IsLeast}$, each entry is two assertions:
--
--   1. **Sufficiency.** Every probabilistic spherical $G_d$-design $\mu$ on $S^{d-1}$ satisfies $f_{\mu,1/d}(x)<f_{\mu,1/d}(0)$ for all $x\ne 0$.
--   2. **Minimality.** For every odd $k$ with $3\le k< G_d$ the corresponding guarantee fails: some probabilistic spherical $k$-design has a point of strictly larger smoothed density than the centre. (It suffices to exhibit one failing $(G_d-2)$-design, since design classes are nested downwards in strength.)
--
--   Concretely for $d=100$: **every** probabilistic spherical $39$-design in $\mathbb{R}^{100}$ has a unique central global mode at variance $1/100$, while **some** finitely supported positively weighted spherical $37$-design in $\mathbb{R}^{100}$ has a noncentral point whose smoothed density at variance $1/100$ strictly exceeds its central density.
--
--   ## How it is proved (on paper)
--
--   The upper half reduces, by a classical paired Lobatto/Radau quadrature extremality argument, to a one-variable inequality: with $\pi_{d,m}$ the canonical $(m{+}2)$-node Lobatto projection law (pole mass $w=\tfrac12\binom{d+m-1}{m}^{-1}$ at each of $\pm 1$), $M(t)=\mathbb{E}_{\pi}e^{tZ}$, and $G(t)=e^{t^{2}/(2d)}$, universal strict central global maximality at variance $1/d$ is equivalent to
--   $$M(t) < G(t)\qquad\text{for all } t>0 .$$
--   This is established for $G_d=2m+1$ by fourteen exact interval bounds per dimension: a small-tilt bound on $(0,d/4]$ from the coefficientwise moment-gap estimates $0\le M-S\le p\{\cosh t-1-t^2/2\}$ and $G-S\ge t^4/[4d^2(d+2)]$; twelve interval bounds on $[jd/16,(j+1)d/16]$, $j=4,\dots,15$, using strict monotonicity of $S/G$; and a tail bound on $[d,\infty)$. Minimality follows from the pole obstruction $w_-e^{d/2}>1$ with $w_-=[2\binom{d+m-2}{m-1}]^{-1}$ at the preceding odd strength $2m-1$, realised by an explicit finite positively weighted spherical lift. In total **ninety exact rational inequalities** across the six dimensions, all verified in exact `Fraction` arithmetic and independently audited (verdict PASS).
--
--   ## What is *not* claimed
--
--   * **This is not a claim of unique criticality, nor of a unique local mode.** A $39$-design in $\mathbb{R}^{100}$ may well possess further local modes and further critical points of $f_{\mu,1/100}$; the statement only says the origin is the unique *global* maximiser. The least strengths $L_d$ (zero is the only local mode) and $Q_d$ (zero is the only critical point) are strictly larger — asymptotically $\approx 0.49636\,d$ versus $\approx 0.35579\,d$ for $G_d$ — and are **not** determined here.
--   * No assertion is made for any dimension outside the six listed values, and no interpolation or formula in $d$ is claimed.
--   * Minimality is asserted over the full probabilistic / positively weighted class. The counterexamples used are weighted; the source report for these cutoffs explicitly leaves minimality *within the equal-weight subclass* unproved (sufficiency of course covers equal-weight designs, as they are probabilistic designs).
--   * The unit sphere is fixed. Scaling the sphere by radius $R$ multiplies the critical variance by $R^{2}$ and leaves the strength table unchanged, but that scaling statement is a separate remark and is not part of what is asserted here.
--   * The paper proof is an exact-rational certificate attached to a written analytic argument; it is not itself a proof-assistant verification. Formalising it is exactly the task posed.
-- source:
--   reports/odd_design_global_cutoffs.md, "Six exact finite-dimensional global-mode strength cutoffs" (2026-09-19): headline table (G_d = 13, 21, 39, 75, 111, 183 for d = 25, 50, 100, 200, 300, 500), Section 1 "Analytic reduction", Section 2 "A finite collection of inequalities covers all positive tilts" eqs. (3)-(6), Section 3 "Exact rational evaluation" (90 exact rational inequalities); certificate reports/odd_design_global_cutoffs_certificate.json produced by experiments/verify_odd_design_global_cutoffs.py. Cross-referenced at reports/RESEARCH_STATUS.md line 42. Independently audited PASS in reports/odd_design_global_cutoffs_audit.md (2026-09-19). Supporting all-design extremality and the definition of the smoothing/mode notions: reports/odd_design_noise_theorem.md, sections "Simultaneous extremality over the entire moment class" (eq. 3) and "Exact universal threshold statements, including boundary qualifications" (eq. 6); moment-gap inputs: reports/odd_design_sharp_strength.md, eqs. (6) and (11).

import Mathlib
open MeasureTheory

namespace OddDesignGlobalCutoff

theorem isLeast_odd_strength_unique_central_global_mode
    (d G : ℕ)
    (hdG : (d, G) ∈ [(25, 13), (50, 21), (100, 39), (200, 75), (300, 111), (500, 183)])
    (σ : Measure (EuclideanSpace ℝ (Fin d)))
    (hσ : σ =
      Measure.map
        (Subtype.val :
          ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) → EuclideanSpace ℝ (Fin d))
        ((((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere Set.univ)⁻¹) •
          (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere)) :
    IsLeast
      {k : ℕ |
        3 ≤ k ∧ Odd k ∧
          ∀ μ : Measure (EuclideanSpace ℝ (Fin d)),
            IsProbabilityMeasure μ →
            μ (Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) = 1 →
            (∀ p : MvPolynomial (Fin d) ℝ,
              p.totalDegree ≤ k →
              ∫ x, MvPolynomial.eval (fun i => x i) p ∂μ =
                ∫ x, MvPolynomial.eval (fun i => x i) p ∂σ) →
            ∀ x : EuclideanSpace ℝ (Fin d), x ≠ 0 →
              ∫ y, Real.exp (-(d : ℝ) * ‖x - y‖ ^ 2 / 2) ∂μ <
                ∫ y, Real.exp (-(d : ℝ) * ‖y‖ ^ 2 / 2) ∂μ}
      G := by sorry

end OddDesignGlobalCutoff
