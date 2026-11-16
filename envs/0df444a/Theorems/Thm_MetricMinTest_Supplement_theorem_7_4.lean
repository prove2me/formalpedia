-- Prove2me | Theorems.Thm_MetricMinTest_Supplement_theorem_7_4
-- name    : MetricMinTest.Supplement.theorem_7_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:44:42.713936+00:00
-- url     : https://prove2.me/theorems/7691a772-9456-411b-add7-4873f54e8b7d
-- title:
--   Theorem 7.4, pp.17–18 — regional workload on homogeneous metrics: $H=k/(\gamma^2D)$, $J=\min\{F,H(1+\ln D)\}$
-- statement:
--   Let $d$ be a metric on $k\ge1$ points whose isometry group acts transitively, let $\gamma\in(0,1/4]$, and suppose $d(i,j)\ge\gamma/2$ for distinct $i,j$. Put
--   $$\kappa=\sum_j(\gamma-d(i,j))_+^2,\qquad D=\kappa/\gamma^2,$$
--   which are independent of $i$. Then
--   $$H_d(\gamma)=\frac{k}{\gamma^2D},\qquad J_d(\gamma)=\min\{F_d(\gamma),\ H_d(\gamma)(1+\ln D)\}.$$
--
--   On symmetric metrics the regional workload is thus the better of ball certificates and one whole-space screening region; Corollary 7.6 applies it to $d_m$.
--
--   **Formalization Note** Transitivity of the isometry group: for all $i,i'$ there is a distance-preserving bijection mapping $i$ to $i'$.
--
--   Differences from the source:
--   - encoding: a metric on $k\ge1$ points → a pseudometric with $d(i,j)=0\Rightarrow i=j$ on a finite nonempty index type; reason: definition of a metric
--   - encoding: standing $\gamma\in(0,1/4]$ (§2) → hypothesis $\gamma\in(0,1/4]$; reason: standing assumption
--   - encoding: isometry group acts transitively → for all $i,i'$ a bijection $\sigma$ with $d(\sigma x,\sigma y)=d(x,y)$ and $\sigma i=i'$; reason: definition
--   - encoding: $\kappa$, $D$ independent of $i$; formulas in terms of them → first conclusion: equal $\kappa$ at all points; formulas with $\kappa$, $D$ computed at any point $i$; reason: same content
--   - encoding: admissible regions $(Z,r)$, $r<\gamma$ an occurring distance → regions indexed by $(Z,(i_0,j_0))$ with radius $d(i_0,j_0)$; reason: every occurring distance is available; duplicated regions have equal cost, so $J$ is unchanged
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Theorem 7.4, pp.17–18

import Mathlib
import Definitions.Def_MetricMinTest_IsPseudometric
import Definitions.Def_MetricMinTest_infoWorkload
import Definitions.Def_MetricMinTest_certWorkload
import Definitions.Def_MetricMinTest_Supplement_mixedWorkload

namespace MetricMinTest.Supplement

/-- **Theorem 7.4 (Regional workload on homogeneous metrics).** Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Theorem 7.4, pp.17–18: "Let d
be a metric on k ≥ 1 points whose isometry group acts transitively, and suppose d(i, j) ≥ γ/2 for
distinct i, j. Put κ = ∑_j (γ − d(i, j))₊², D = κ/γ², which are independent of i. Then
H_d(γ) = k/(γ²D), J_d(γ) = min{F_d(γ), H_d(γ)(1 + ln D)}."

**Formalization Note.** A metric is a pseudometric with `d i j = 0 → i = j`; `k = |ι| ≥ 1`
(`Nonempty`). Transitivity of the isometry group: for all `i, i'` a bijection `σ` of the
points with `d(σx, σy) = d(x, y)` and `σ i = i'`. Standing `γ ∈ (0, 1/4]` (§2). "Independent of
`i`" is the first conclusion (equal `κ` at all points); the formulas hold with `κ, D` computed at
any point `i`. `J = mixedWorkload`. -/
theorem theorem_7_4 {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] (d : ι → ι → ℝ)
    (hd : IsPseudometric d) (hmet : ∀ i j, d i j = 0 → i = j)
    (htrans : ∀ i i' : ι, ∃ σ : ι ≃ ι, (∀ x y, d (σ x) (σ y) = d x y) ∧ σ i = i')
    (γ : ℝ) (hγ : γ ∈ Set.Ioc (0 : ℝ) (1 / 4)) (hsep : ∀ i j, i ≠ j → γ / 2 ≤ d i j) :
    (∀ i i', ∑ j, (max (γ - d i j) 0) ^ 2 = ∑ j, (max (γ - d i' j) 0) ^ 2) ∧
    ∀ i, infoWorkload d γ =
        (Fintype.card ι : ℝ) / (γ ^ 2 * ((∑ j, (max (γ - d i j) 0) ^ 2) / γ ^ 2)) ∧
      mixedWorkload d γ = min (certWorkload d γ)
        (infoWorkload d γ * (1 + Real.log ((∑ j, (max (γ - d i j) 0) ^ 2) / γ ^ 2))) := by sorry

end MetricMinTest.Supplement
