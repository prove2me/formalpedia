-- Prove2me | Theorems.Thm_IntermediateDisorder_PointToLine_rhoK_fock_summable
-- name    : IntermediateDisorder.PointToLine.rhoK_fock_summable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:24:18.086132+00:00
-- url     : https://prove2.me/theorems/b08da4d2-a76c-4fc2-ad23-d83a0613524f
-- title:
--   §3.4 and Lemma 3.1 — $\|\varrho_k\|_{L^2}^2=1/(2^k\Gamma(k/2+1))$ and $\mathcal Z_\beta=I(\boldsymbol\varrho(\beta))$ is well defined
-- statement:
--   For every $k\ge0$ the Brownian transition kernel $\varrho_k$ (extended by zero off $\Delta_k\times\mathbb R^k$) lies in $L^2([0,1]^k\times\mathbb R^k)$ and
--
--   $$\int_{\Delta_k}\int_{\mathbb R^k}\varrho_k(\mathbf t,\mathbf x)^2\,d\mathbf x\,d\mathbf t=\frac1{2^k\,\Gamma(k/2+1)} .$$
--
--   Consequently, for every white noise $W$ on $[0,1]\times\mathbb R$ with multiple stochastic integrals $I=(I_k)$ and every $\beta\in\mathbb R$, the series $\sum_{k\ge0}\beta^kI_k(\varrho_k)$ converges in $L^2(Q')$ — so the Wiener chaos $\mathcal Z_\beta=I(\boldsymbol\varrho(\beta))$ of (7), with $\boldsymbol\varrho(\beta)=(1,\beta\varrho_1,\beta^2\varrho_2,\dots)$, is well defined — and
--
--   $$E\big[\mathcal Z_\beta^2\big]=\sum_{k\ge0}\frac{\beta^{2k}}{2^k\,\Gamma(k/2+1)} .$$
--
--   This is what makes the limit object of the whole mission meaningful: the norms decay fast enough in $k$ for $\boldsymbol\varrho(\beta)$ to lie in the Fock space for all $\beta$. For $k=1$ the value $1/\sqrt\pi$ matches the variance $2\beta^2/\sqrt\pi=(\sqrt2\beta)^2\|\varrho_1\|^2$ of the first-order term on p. 6.
--
--   **Formalization Note** The second-moment identity is the isometry of the Fock map (§3.3) applied to $\boldsymbol\varrho(\beta)$; it states the content of "$\mathcal Z_\beta=I(\boldsymbol\varrho(\beta))$" in this formalization, where $\mathcal Z_\beta$ is defined as $I(\boldsymbol\varrho(\beta))$. The membership $\varrho_k\in L^2$ and the summability rule out the default values of the definitions.
-- source:
--   Alberts, Khanin, Quastel, The intermediate disorder regime for directed polymers in dimension 1+1, arXiv:1202.4398v3, p. 20, §3.4 (display computing ∫_{Δ_k}∫ϱ_k² ) and Lemma 3.1

import Mathlib
import Definitions.Def_IntermediateDisorder_PointToLine_WienerChaos

namespace IntermediateDisorder.PointToLine

open MeasureTheory ProbabilityTheory

/-- §3.4 and Lemma 3.1: `ϱ_k ∈ L²([0,1]^k × ℝ^k)` with
`‖ϱ_k‖² = 1 / (2^k Γ(k/2 + 1))`; consequently, for every white noise `W` with multiple
integrals `I` and every `β ∈ ℝ`, the series `∑_k β^k I_k(ϱ_k)` defining `𝒵_β = I(ϱ(β))`
converges in `L²`, and `E[𝒵_β²] = ∑_k β^{2k} ‖ϱ_k‖²`. -/
theorem rhoK_fock_summable {Ω' : Type*} [MeasurableSpace Ω'] {Q' : Measure Ω'}
    [IsProbabilityMeasure Q'] (W : Set (ℝ × ℝ) → Ω' → ℝ)
    (I : (k : ℕ) → Lp ℝ 2 (kernelMeasure k) →L[ℝ] Lp ℝ 2 Q')
    (hW : IsWhiteNoise W Q') (hI : IsMultipleIntegral W Q' I) :
    (∀ k : ℕ, MemLp (rhoK k) 2 (kernelMeasure k) ∧
      ∫ z, rhoK k z ^ 2 ∂(kernelMeasure k) = 1 / (2 ^ k * Real.Gamma ((k : ℝ) / 2 + 1))) ∧
    ∀ β : ℝ, Summable (fun k : ℕ => I k (β ^ k • rhoKLp k)) ∧
      ∫ a, wienerChaos I β a ^ 2 ∂Q' =
        ∑' k : ℕ, β ^ (2 * k) / (2 ^ k * Real.Gamma ((k : ℝ) / 2 + 1)) := by sorry

end IntermediateDisorder.PointToLine
