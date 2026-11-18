-- Prove2me | Theorems.Thm_LocalOccupancyIS_Glauber_rounded_finite_certificate
-- name    : LocalOccupancyIS.Glauber.rounded_finite_certificate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T02:32:39.219947+00:00
-- url     : https://prove2.me/theorems/454cac25-af2b-47ce-8976-f1a0989237eb
-- title:
--   Finite-time local occupancy after rounding the fugacity
-- statement:
--   Let $G$ be a nonempty finite graph whose degrees are at most $\Delta\ge1$. Let $t\ge1$ and $b\ge0$ satisfy the hereditary neighborhood-density hypothesis, and put $s=(b+1)^{1/(2t-1)}$, $D=\log(\Delta/s)$, $\lambda=1/(sD^{2t-1})$ and $C=4(16e+3)$. Assume
--
--   $$D\ge1000et,\qquad\frac{t\log D}{D}\le\frac1C.$$
--
--   For any real $q$ with $sD^{2t-1}\le q\le sD^{2t-1}+2$, set $\widehat\lambda=1/q$ and recompute the occupancy optimizer while retaining the prescribed correction $c$. Then
--
--   $$\left|\frac{\widehat\lambda}{\lambda}-1\right|\le\frac2D,\qquad\left|\frac{\widehat\Gamma D}{\Delta}-1\right|\le C\frac{t\log D}{D}.$$
--
--   For every supplied neighborhood sweep order, the rounded parameters also satisfy the complete finite conclusion: positive occupancy parameters, the arbitrary-input certificate at the second and third sweeps, occurrence bound at most $3\Delta$, the finite-time ordinary-Glauber expected-size bound, and its largest-set repetition amplification. In particular,
--
--   $$T\ge\frac{C_3^2H_{\widehat\lambda}}{2\varepsilon^2}\quad\Longrightarrow\quad\mathbb E|I_J|\ge(1-\varepsilon)\frac n{\widehat\Gamma}.$$
--
--   This stability result allows the actual rational preprocessing output to replace the ideal-real fugacity in Corollary 4 without losing its leading occupancy constant or its finite-time guarantee.
--
--   Here the finite-time assertion has $0<\varepsilon<1$, a positive integer $T$, and an independent uniform index $J$ in the first $T$ times, from every supplied initial independent set.
-- source:
--   Davies and Tan, Large independent sets via neighborhood block dynamics, Glauber dynamics, and local occupancy, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/982.pdf, Corollary 4 and Remark 1 p.6, Proposition 6, Lemmas 9 and 11, Theorem 2, implementation §§6 pp.19–20; quantitative rounding and parameterStage conventions in the mission BitExecution and GoalInterface definitions.

import Definitions.Def_LocalOccupancyIS_Glauber_GoalInterface

namespace LocalOccupancyIS.Glauber
theorem rounded_finite_certificate (n Δ t : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (b q : ℝ)
    (hn : 0 < n) (hΔ : 1 ≤ Δ) (ht : 1 ≤ t) (hb : 0 ≤ b) (hbound : DegreeBound G Δ)
    (hd : HereditaryDensity G t b) (hD : 1000*Real.exp 1*t ≤ D Δ t b)
    (hqlo : scale t b*D Δ t b^(2*t-1) ≤ q) (hqhi : q ≤ scale t b*D Δ t b^(2*t-1)+2)
    (hsmall : relativeError Δ t b ≤ 1/(4*(16*Real.exp 1+3)))
    (w : Fin n → List (Fin n)) (hw : ∀ u, IsSweep (G.neighborFinset u) (w u)) :
    |(1/q)/fugacity Δ t b-1| ≤ 2/D Δ t b ∧
    FiniteConclusion G Δ (1/q) (correction Δ t b) w ∧
    |Gamma Δ (1/q) (correction Δ t b)*D Δ t b/Δ-1| ≤
      (4*(16*Real.exp 1+3))*relativeError Δ t b := by sorry
end LocalOccupancyIS.Glauber
