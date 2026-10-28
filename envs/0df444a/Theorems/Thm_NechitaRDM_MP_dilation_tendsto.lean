-- Prove2me | Theorems.Thm_NechitaRDM_MP_dilation_tendsto
-- name    : NechitaRDM.MP.dilation_tendsto
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:48:37.30833+00:00
-- url     : https://prove2.me/theorems/9c92c5a5-444f-4749-adf4-5aebada15e54
-- title:
--   Proof of Theorem 5, eqs. (51)–(53), p. 14 — perturbing the atoms by factors tending to 1 does not change a compactly supported weak limit
-- statement:
--   Let $(\mu_n)_n$ be measures on $\mathbb R$ converging weakly to a probability measure $\nu$ with compact support, in the sense that $\int f\,d\mu_n \to \int f\,d\nu$ for every bounded continuous $f$. Let $t_n \to 1$ be real numbers and let $\mu_n^{t_n}$ be the image of $\mu_n$ under $x \mapsto t_n x$ (for an empirical measure, every Dirac mass $\delta_x$ is replaced by $\delta_{t_n x}$). Then
--   $$\int f\,d\mu_n^{t_n} \longrightarrow \int f\,d\nu \qquad \text{for every bounded continuous } f .$$
--
--   In the proof of Theorem 5 it is applied pathwise with $\mu_n = L_n^W$, $\nu = \mu_c$ (supported in $[0, (\sqrt c+1)^2]$) and $t_n = cn^2/S_n$: "such a perturbation does not change the limit in distribution".
--
--   **Formalization Note** The paper argues through moments; this milestone states the claim the proof needs, with the paper's compact-support assumption on the limit, as a deterministic fact about measures.
-- source:
--   Nechita, Asymptotics of random density matrices, arXiv:quant-ph/0702154v3, p. 14, proof of Theorem 5, eqs. (51)–(53)

import Mathlib
import Definitions.Def_NechitaRDM_MP_Basic

namespace NechitaRDM.MP

open MeasureTheory Filter Topology

/-- **Proof of Theorem 5, eqs. (51)–(53)** (p. 14). If measures `μₙ` on `ℝ` converge weakly to a
compactly supported probability measure `ν`, and the atoms are perturbed by factors `tₙ → 1`
(`x ↦ tₙ x`), the perturbed measures still converge weakly to `ν`. -/
theorem dilation_tendsto (μ : ℕ → Measure ℝ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ∃ K : Set ℝ, IsCompact K ∧ ν Kᶜ = 0)
    (hμ : ∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n => ∫ x, f x ∂(μ n)) atTop (𝓝 (∫ x, f x ∂ν)))
    (t : ℕ → ℝ) (ht : Tendsto t atTop (𝓝 1)) :
    ∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n => ∫ x, f x ∂((μ n).map fun x => t n * x)) atTop
        (𝓝 (∫ x, f x ∂ν)) := by sorry

end NechitaRDM.MP
