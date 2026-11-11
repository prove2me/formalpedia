-- Prove2me | Theorems.Thm_GaussDiffSVP_lemma_9_2
-- name    : GaussDiffSVP.lemma_9_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:59:29.860527+00:00
-- url     : https://prove2.me/theorems/39cb29d6-fa0f-4ac2-abe1-e5ea9847585a
-- title:
--   Lemma 9.2 — target success $\Pr[G, Z_v>0]\ge\frac{g^2}6e^{-6D}\min\{1,\Lambda\}$
-- statement:
--   Fix the scale, prime and $\delta$. Let $G$ depend only on $\Gamma$ with $g = \Pr[G]>0$, and let $\mu = \mu_\delta$ and $\xi$ be as in Theorem 9.1 ($\mathbb E_z[J\mid\Gamma] = \mu$ for every $\Gamma$, $\mathbb E[J^2]\le(1+\xi)\mu^2+\mu$), with $\mu\ge1$ and $\xi\le1$. Conditional on each environment $(\Gamma,z,\delta)$ in $G$, suppose the two record lists are independent, supported on $C\cap S_r(a)$, and satisfy with uniform $A>0$, $D\ge0$
--   $$e^{-D}A\le m_\pm(x)\le e^DA,\qquad S_\pm(x,x')\le e^DA^2\qquad(x,x'\in C\cap S_r(a)).$$
--   Let $Z_v$ count record pairs with difference $v$, $Y = \mathbf 1_GZ_v$ and $\Lambda = A^2\mu$. Then
--   $$\mathbb E[Y]\ge ge^{-2D}\Lambda,\qquad\mathbb E[Y^2]\le e^{2D}(4\Lambda^2+2\Lambda),\qquad\Pr[G,Z_v>0]\ge\frac{g^2}6e^{-6D}\min\{1,\Lambda\}.$$
--   If $g = 1-o(1)$, $\Lambda\ge e^{-o(n)}$ and $D = o(n)$, this is $e^{-o(n)}$. It turns the coset count of Theorem 9.1 into a target occurrence using only the first two factorial measures.
--
--   Differences from the source:
--   - generalization: the concrete environments $(\Gamma,z,\delta)$, $C\cap S_r(a)$ and $\mu$, $\xi$ of Theorem 9.1 → arbitrary independent environment laws, arbitrary supports, and the two properties of $J$ used by the proof as hypotheses; reason: the concrete setting is the instance given by Theorem 9.1
--   - encoding: supported on $C\cap S_r(a)$ → intensity zero outside the support; reason: same instances
--   - encoding: the final sentence → a separate conjunct for sequences $g_n\to1$, $\Lambda_n\ge e^{-f(n)}$ with $f = o(n)$, $D_n = o(n)$; reason: explicit quantifiers
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Lemma 9.2, p.43

import Mathlib
import Definitions.Def_GaussDiffSVP_intensity
import Definitions.Def_GaussDiffSVP_factMoment

open Filter Topology
open scoped ENNReal

namespace GaussDiffSVP

/-- Lemma 9.2 (Target success) (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), p.43), in abstract form. Environments are pairs `(i, y)` —
`i` the line `Γ`, `y` the coset shift `z` — drawn independently from `ω_I` and `ω_Z` (`δ` fixed). For
each environment let `C ∩ S_r(a)` be the support `Sup(i, y)` and
`J = |{x ∈ Sup : x − v ∈ Sup}|`; as in Theorem 9.1, `E_z[J | Γ] = μ` for every `Γ` and
`E[J²] ≤ (1 + ξ)μ² + μ`, with `μ ≥ 1` and `ξ ≤ 1`. Let `G` depend only on `Γ`, with `g = P[G] > 0`.
Conditional on each environment in `G`, the two record lists are independent, supported on
`Sup`, and satisfy, with uniform `A > 0` and `D ≥ 0`,
`e^{−D}A ≤ m_±(x) ≤ e^{D}A`, `S_±(x, x′) ≤ e^{D}A²` for `x, x′ ∈ Sup` (93). Let `Z_v` count record pairs
with difference `v`, `Y = 1_G Z_v` and `Λ = A²μ`. Then
`E[Y] ≥ g e^{−2D}Λ` (94), `E[Y²] ≤ e^{2D}(4Λ² + 2Λ)` (95), and
`P[G, Z_v > 0] ≥ (g²/6) e^{−6D} min{1, Λ}` (96). If `g = 1 − o(1)`, `Λ ≥ e^{−o(n)}` and `D = o(n)`,
this is `e^{−o(n)}`.

**Formalization Note.** Abstract version: the lemma's proof uses Theorem 9.1 only through
`E_z[J | Γ] = μ` and `E[J²] ≤ (1 + ξ)μ² + μ` (from (90)), which are hypotheses here; the concrete
setting (lines `Γ`, `z ∈ K/L`, `C = z + δ + Γ`, `Sup = C ∩ S_r(a)`, `ξ = 2^{−h_n+O(ℓ_n)}`) is the instance
given by Theorem 9.1. Values form an additive group; laws, counts and expectations are in `ℝ≥0∞`;
"supported on" is "intensity zero outside `Sup`". The last sentence is the final conjunct, for
sequences `g_n, Λ_n, D_n`. -/
theorem lemma_9_2 {α I Z : Type*} [AddGroup α] (ωI : PMF I) (ωZ : PMF Z) (G : Set I) (v : α)
    (Sup : I → Z → Set α) (μp μm : I → Z → PMF (List α)) (μ ξ A D : ℝ)
    (hμ : 1 ≤ μ) (hξ : ξ ≤ 1) (hA : 0 < A) (hD : 0 ≤ D)
    (hmean : ∀ i, ∑' y, ωZ y * (({x | x ∈ Sup i y ∧ x - v ∈ Sup i y}.encard : ℕ∞) : ℝ≥0∞) =
      ENNReal.ofReal μ)
    (hsq : ∑' i, ∑' y, ωI i * ωZ y *
        (({x | x ∈ Sup i y ∧ x - v ∈ Sup i y}.encard : ℕ∞) : ℝ≥0∞) ^ 2 ≤
      ENNReal.ofReal ((1 + ξ) * μ ^ 2 + μ))
    (hG : 0 < ωI.toOuterMeasure G)
    (hsupp : ∀ i ∈ G, ∀ y, ∀ x, x ∉ Sup i y →
      intensity (μp i y) x = 0 ∧ intensity (μm i y) x = 0)
    (hmom : ∀ i ∈ G, ∀ y, ∀ x ∈ Sup i y, ∀ x' ∈ Sup i y,
      ENNReal.ofReal (Real.exp (-D) * A) ≤ intensity (μp i y) x ∧
      intensity (μp i y) x ≤ ENNReal.ofReal (Real.exp D * A) ∧
      ENNReal.ofReal (Real.exp (-D) * A) ≤ intensity (μm i y) x ∧
      intensity (μm i y) x ≤ ENNReal.ofReal (Real.exp D * A) ∧
      factMoment (μp i y) x x' ≤ ENNReal.ofReal (Real.exp D * A ^ 2) ∧
      factMoment (μm i y) x x' ≤ ENNReal.ofReal (Real.exp D * A ^ 2)) :
    let g := (ωI.toOuterMeasure G).toReal
    let Λ := A ^ 2 * μ
    let Zv : List α → List α → ℝ≥0∞ := fun l₁ l₂ =>
      (({ab : Fin l₁.length × Fin l₂.length | l₁.get ab.1 - l₂.get ab.2 = v}.encard : ℕ∞) : ℝ≥0∞)
    let EG : (List α → List α → ℝ≥0∞) → ℝ≥0∞ := fun F =>
      ∑' i, ∑' y, ωI i * ωZ y * G.indicator (fun i => ∑' l₁, ∑' l₂,
        μp i y l₁ * μm i y l₂ * F l₁ l₂) i
    ENNReal.ofReal (g * Real.exp (-(2 * D)) * Λ) ≤ EG Zv ∧
    EG (fun l₁ l₂ => Zv l₁ l₂ ^ 2) ≤ ENNReal.ofReal (Real.exp (2 * D) * (4 * Λ ^ 2 + 2 * Λ)) ∧
    ENNReal.ofReal (g ^ 2 / 6 * Real.exp (-(6 * D)) * min 1 Λ) ≤
      EG (fun l₁ l₂ => if Zv l₁ l₂ = 0 then 0 else 1) ∧
    (∀ gs Λs Ds : ℕ → ℝ, Tendsto gs atTop (𝓝 1) → (∀ n, 0 ≤ Ds n) →
      Tendsto (fun n : ℕ => Ds n / n) atTop (𝓝 0) →
      (∃ f : ℕ → ℝ, Tendsto (fun n : ℕ => f n / n) atTop (𝓝 0) ∧ ∀ n, Real.exp (-f n) ≤ Λs n) →
      ∃ f : ℕ → ℝ, Tendsto (fun n : ℕ => f n / n) atTop (𝓝 0) ∧ ∀ᶠ n in atTop,
        Real.exp (-f n) ≤ gs n ^ 2 / 6 * Real.exp (-(6 * Ds n)) * min 1 (Λs n)) := by sorry

end GaussDiffSVP
