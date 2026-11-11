-- Prove2me | Theorems.Thm_LogLogJam_lemma_5_3
-- name    : LogLogJam.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:21:52.834024+00:00
-- url     : https://prove2.me/theorems/3d047135-2ddc-4576-8b41-77e3ed577032
-- title:
--   Lemma 5.3 — the success set has measure at most $2\pi\varepsilon/E$
-- statement:
--   Let $\lambda>1$ with energy $E=\tfrac14(\lambda+\lambda^{-1})>1$, let $\varepsilon\in(0,1/2)$ and $\theta\in\mathbb T$. The **success set** $A_\varepsilon(\theta)=\{\theta'\in\mathbb T: D_{\mathrm{tr}}(\rho_{\theta'},\rho_\theta)\le\varepsilon\}$ has Lebesgue measure
--
--   $$
--   |A_\varepsilon(\theta)|\le\frac{2\pi\varepsilon}{E}.
--   $$
--
--   To estimate the state to trace distance $\varepsilon$ a learner must locate $\theta$ to precision $O(\varepsilon/E)$: high energy makes the state sensitive to the angle.
--
--   Differences from the source:
--
--   - encoding: $\theta\in\mathbb T=\mathbb R/\pi\mathbb Z$, uniform law and integrals on $\mathbb T$ → $\theta\in\mathbb R$ with $\pi$-periodic objects; uniform law and integrals over $[0,\pi)$; reason: $V_{\lambda,\theta}$ is $\pi$-periodic, so $[0,\pi)$ is one period; same instances
--   - encoding: the trace distance $D_{\mathrm{tr}}(\rho_{\theta'},\rho_\theta)$ of quantum states → $\sqrt{1-2/\sqrt{\det(V_{\lambda,\theta}+V_{\lambda,\theta'})}}$; reason: Lemma 4.1 (pp.15–16) for pure zero-mean single-mode Gaussian states; same values
--   - encoding: energy $E>1/2$ and $\lambda>1$ the solution of $E=\tfrac14(\lambda+\lambda^{-1})$ → $\lambda>1$ as the parameter, $E=\mathrm{energy}\,\lambda=(\lambda+\lambda^{-1})/4$; reason: $\lambda\mapsto(\lambda+\lambda^{-1})/4$ is a bijection from $(1,\infty)$ onto $(1/2,\infty)$; same instances
-- source:
--   Chen, Gong, Ye, Zhang, The log log jam in Gaussian state tomography, arXiv:2607.12983 (version of November 3, 2026, sha256 97b751ca…), Lemma 5.3, p.22 (PDF p.25)

import Mathlib
import Definitions.Def_LogLogJam_Vsq

open MeasureTheory

namespace LogLogJam

/-- **Lemma 5.3** (arXiv:2607.12983, version of November 3, 2026, sha256 97b751ca…, Lemma 5.3, p.22): "For ε ∈ (0, 1/2), E > 1, and θ ∈ 𝕋, we have
|A_ε(θ)| ≤ 2πε/E", where `A_ε(θ) = {θ' ∈ 𝕋 | D_tr(ρ_{θ'}, ρ_θ) ≤ ε}` and `|·|` is Lebesgue measure.

**Formalization Note** `𝕋 = ℝ/πℤ` is represented by the period `[0, π)`; `E = energy lam` with
`lam > 1` the squeezing parameter of §5.1. -/
theorem lemma_5_3 (lam ε θ : ℝ) (hlam : 1 < lam) (hE : 1 < energy lam) (hε : 0 < ε)
    (hε2 : ε < 1 / 2) :
    volume {θ' ∈ Set.Ico 0 Real.pi | trDist lam θ' θ ≤ ε} ≤
      ENNReal.ofReal (2 * Real.pi * ε / energy lam) := by sorry

end LogLogJam
