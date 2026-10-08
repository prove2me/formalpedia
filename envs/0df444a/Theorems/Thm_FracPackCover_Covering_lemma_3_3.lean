-- Prove2me | Theorems.Thm_FracPackCover_Covering_lemma_3_3
-- name    : FracPackCover.Covering.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:46:55.194874+00:00
-- url     : https://prove2.me/theorems/db897831-824e-4d77-bb5d-11407ec22d2f
-- title:
--   Lemma 3.3 — a step toward the maximum-cost point lowers $\Phi$ by at least $\varepsilon\alpha\sigma\Phi$
-- statement:
--   Let $A\ge0$, $b>0$, $P$ be covering data and $\rho>0$ a bound on the width ($a_ix\le\rho\,b_i$ for all $x\in P$ and all $i$). Let $x\in P$, $0<\varepsilon\le1$ and $\alpha>0$; let $y_i=\frac1{b_i}e^{-\alpha a_ix/b_i}$ be the dual solution corresponding to $x$ and $\Phi=y^tb$ its potential. Suppose $x$ and $y$ do not satisfy $\mathcal C2$. Let $\tilde x\in P$ attain the maximum $C_{\mathcal C}(y)$ of $y^tAx$ over $P$, and let $0\le\sigma\le\varepsilon/(4\alpha\rho)$. Put $\hat x=(1-\sigma)x+\sigma\tilde x$ and let $\hat\Phi$ be the potential of $\hat x$ (same $\alpha$). Then
--   $$\Phi-\hat\Phi\ \ge\ \varepsilon\alpha\sigma\,\Phi .$$
--
--   This is the progress lemma of the covering algorithm: as long as $\mathcal C2$ fails, every update of IMPROVE-COVER decreases the potential by a constant factor.
--
--   **Formalization Note** The step $\sigma$ is assumed nonnegative, as it is in Figure 3.
-- source:
--   Plotkin, Shmoys, Tardos, Fast Approximation Algorithms for Fractional Packing and Covering Problems, Cornell ORIE Tech. Rep. 999 (1992), p. 19, Lemma 3.3

import Mathlib
import Definitions.Def_FracPackCover_Covering_Basic

namespace FracPackCover.Covering

/-- Lemma 3.3 (Plotkin–Shmoys–Tardos, Cornell ORIE TR 999, p. 19). Let `x ∈ P`, `0 < ε ≤ 1`,
`α > 0`, and let `y` be the dual solution corresponding to `x` (parameter `α`), with potential
`Φ = yᵗb`, such that `x, y` do not satisfy 𝒞2. Let `x̃ ∈ P` attain the maximum `C_𝒞(y)` of `yᵗ A x`
over `P`, let `ρ` bound the width, and let `0 ≤ σ ≤ ε/(4αρ)`. For `x̂ = (1 − σ) x + σ x̃` with
potential `Φ̂` (same `α`), `Φ − Φ̂ ≥ ε α σ Φ`. -/
theorem lemma_3_3 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (hdata : IsCoveringData A b P) (ρ : ℝ) (hρ : WidthBound A b P ρ)
    (x xt : Fin n → ℝ) (hx : x ∈ P) (hxt : xt ∈ P)
    (ε α σ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hα : 0 < α) (hσ0 : 0 ≤ σ)
    (hσ : σ ≤ ε / (4 * α * ρ))
    (hmax : ∀ x' ∈ P, yAx A (dualY A b α x) x' ≤ yAx A (dualY A b α x) xt)
    (hC2 : ¬ C2 A b ε (dualY A b α x) x (yAx A (dualY A b α x) xt)) :
    ε * α * σ * potential A b α x ≤
      potential A b α x - potential A b α ((1 - σ) • x + σ • xt) := by sorry

end FracPackCover.Covering
