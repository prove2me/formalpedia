-- Prove2me | Theorems.Thm_LearnManip_gaussian_tilting
-- name    : LearnManip.gaussian_tilting
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:54:57.785363+00:00
-- url     : https://prove2.me/theorems/66fa08c4-4d2e-440e-9124-f5e0a16f3165
-- title:
--   (53)–(54), pp.34–35 (corrected: the relative entropy term of the display) — Gaussian tilting
-- statement:
--   Let $N=N(\mu,v)$ with $v\ge0$, $a\in\mathbb R$, $\gamma>0$. The exponential tilt of $N$ by $ay/\gamma$ is the normal law $N(\mu+av/\gamma,\,v)$, and it has density
--   $$\exp\Bigl(\frac{a(y-\mu)}{\gamma}-\frac{a^2v}{2\gamma^2}\Bigr)$$
--   with respect to $N$. Its relative entropy from $N$ is $a^2v/(2\gamma^2)$, and it attains
--   $$a\,E[y]-\gamma D=a\mu+\frac{a^2v}{2\gamma}=\gamma\log E_N\bigl[e^{ay/\gamma}\bigr].$$
--   For every probability $G\ll N$ with $y$ $G$-integrable and finite relative entropy,
--   $$a\,E_G[y]-\gamma D(G\|N)\le a\mu+\frac{a^2v}{2\gamma},$$
--   with equality iff $G$ is this normal law.
--
--   With $a=1/(1-\alpha)$ this is the optimal distortion $\Lambda^*_q$ at a given quantity $q$, and the origin of the mean boost. The case $v=0$ is included; both laws are then the Dirac mass at $\mu$.
--
--   Differences from the source:
--   - correction: the display on p.35 has the term γ(σ²/(2γ(1−α)))²·1/(2σ²) → the relative entropy a²v/(2γ²), that is γ(σ²/(γ(1−α)))²·1/(2σ²); reason: with the printed term the first line equals µ/(1−α) + 7σ²/(8γ(1−α)²), not the next line µ/(1−α) + σ²/(2γ(1−α)²)
--   - generalization: the reward µ^q/(1−α) → the reward a y for every a ∈ ℝ; reason: a = 1/(1−α) is the source's case
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), proof of Theorem 2, (53)–(54) and the displays below them, pp.34–35

import Mathlib

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory InformationTheory Filter

namespace LearnManip

/-- The Gaussian tilting of the proof of Theorem 2, (53)–(54) and the unnumbered displays, pp.34–35,
of Keppo, Kim, Zhang (SSRN 3465030, 2021-09-04), for an affine reward `a y`: the exponential tilt of
`N(μ, v)` by `a y/γ` is `N(μ + a v/γ, v)`, with density `exp(a(y−μ)/γ − a²v/(2γ²))` (the paper's `Λ*_q`
at `a = 1/(1−α)`); it has relative entropy `a²v/(2γ²)` and value `a μ + a²v/(2γ) = γ log E[e^{a y/γ}]`;
and it is the unique maximizer of `a E_G[y] − γ D(G‖N)` among probabilities `G ≪ N` with `y` integrable
and finite relative entropy. `v = 0` is included: both laws are then the Dirac mass at `μ`. -/
theorem gaussian_tilting (μ : ℝ) (v : ℝ≥0) (a : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    (gaussianReal μ v).tilted (fun y => a * y / γ) = gaussianReal (μ + a * v / γ) v ∧
    (gaussianReal μ v).withDensity
        (fun y => ENNReal.ofReal (Real.exp (a * (y - μ) / γ - a ^ 2 * v / (2 * γ ^ 2)))) =
      gaussianReal (μ + a * v / γ) v ∧
    klDiv (gaussianReal (μ + a * v / γ) v) (gaussianReal μ v) =
      ENNReal.ofReal (a ^ 2 * v / (2 * γ ^ 2)) ∧
    a * ∫ y, y ∂gaussianReal (μ + a * v / γ) v
        - γ * (klDiv (gaussianReal (μ + a * v / γ) v) (gaussianReal μ v)).toReal =
      a * μ + a ^ 2 * v / (2 * γ) ∧
    γ * Real.log (∫ y, Real.exp (a * y / γ) ∂gaussianReal μ v) = a * μ + a ^ 2 * v / (2 * γ) ∧
    ∀ (G : Measure ℝ) [IsProbabilityMeasure G], G ≪ gaussianReal μ v →
      Integrable (fun y : ℝ => y) G → klDiv G (gaussianReal μ v) ≠ ∞ →
      a * ∫ y, y ∂G - γ * (klDiv G (gaussianReal μ v)).toReal ≤ a * μ + a ^ 2 * v / (2 * γ) ∧
      (a * ∫ y, y ∂G - γ * (klDiv G (gaussianReal μ v)).toReal = a * μ + a ^ 2 * v / (2 * γ) ↔
        G = gaussianReal (μ + a * v / γ) v) := by sorry

end LearnManip
