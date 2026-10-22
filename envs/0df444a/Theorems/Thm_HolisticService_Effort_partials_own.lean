-- Prove2me | Theorems.Thm_HolisticService_Effort_partials_own
-- name    : HolisticService.Effort.partials_own
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:15:01.171607+00:00
-- url     : https://prove2.me/theorems/4d1ee762-f648-4e08-b028-83460feb9399
-- title:
--   Proof of Proposition 3, p. 28 — ∂δ*ᵢ/∂cᵢ, ∂δ*ᵢ/∂Vᴴᵢ, δ*ᵢ = (A/(σᴴᵢ−σᴸᵢ) + B − σᴸᵢ)/(σᴴᵢ−σᴸᵢ) and ∂δ*ᵢ/∂σᴴᵢ = −(2A + (B − σᴸᵢ)(σᴴᵢ − σᴸᵢ))/(σᴴᵢ − σᴸᵢ)³
-- statement:
--   Assume the standing assumptions, no technical coupling ($\beta_{j,i} = 0$ for $j \ne i$) and the interior condition. Fix a step $i$, write $d_i = \sigma^H_i - \sigma^L_i$, and let $\delta^*$ be the optimal effort of the design problem, viewed as a function of one parameter of step $i$ at a time (all others fixed). Define
--   $$A = \frac{(1-c_i)(V^H_i-V^L_i)}{r}[\mathbf P^{-1}]_{i,i}, \qquad B = \sum_{j\in\mathcal J\setminus i}\frac{(1-c_j)(V^H_j-V^L_j)}{r(\sigma^H_j-\sigma^L_j)}[\mathbf P^{-1}]_{j,i}.$$
--   Then, at the given parameters:
--
--   1. $\partial\delta^*_i/\partial c_i = -\dfrac{V^H_i-V^L_i}{r d_i^2}[\mathbf P^{-1}]_{i,i} < 0$;
--   2. $\partial\delta^*_i/\partial V^H_i = \dfrac{1-c_i}{r d_i^2}[\mathbf P^{-1}]_{i,i} > 0$;
--   3. $A > 0$ and $\delta^*_i = \dfrac{1}{d_i}\Big(\dfrac{A}{d_i} + B - \sigma^L_i\Big)$;
--   4. $$\frac{\partial\delta^*_i}{\partial\sigma^H_i} = -\frac{2A + (B-\sigma^L_i)d_i}{d_i^3}.$$
--
--   These explicit derivatives are the computation behind the own-step part of Proposition 3.
--
--   **Formalization Note** The page prints $A$ with an extra factor $(\sigma^H_i-\sigma^L_i)^2$ in its denominator and $B$ without the factor $1/(\sigma^H_j-\sigma^L_j)$; with the printed $A$ and $B$ the displayed identity for $\delta^*_i$ is false. The corrected $A$ and $B$ above make both the identity and the printed derivative in $\sigma^H_i$ correct. Derivatives are in $c_i$, $V^H_i$ (with $V^L_i$ fixed) and $\sigma^H_i$ (with $\sigma^L_i$ fixed); under no technical coupling $c_i - \sum_{m\ne i}\beta_{i,m} = c_i$.
-- source:
--   Bellos & Kavadias, Service design for a holistic customer experience: a process framework, authors' manuscript (Management Science 2020, doi:10.1287/mnsc.2020.3609), p. 28 (PDF 28), proof of Proposition 3, ∂δ*_i/∂c_i, ∂δ*_i/∂V^H_i, A, B, ∂δ*_i/∂σ^H_i (A and B corrected)

import Mathlib
import Definitions.Def_HolisticService_Effort_Model

namespace HolisticService.Effort

/-- Proof of Proposition 3, p. 28 (own step), with no technical coupling (p. 14): the partial
derivatives of the optimal effort `δ*_i` in `c_i`, `V^H_i` and `σ^H_i`. `A` and `B` are the corrected
quantities `A = (1 − c_i)(V^H_i − V^L_i)[P⁻¹]_{i,i}/r` and
`B = Σ_{j≠i} (1 − c_j)(V^H_j − V^L_j)[P⁻¹]_{j,i}/(r(σ^H_j − σ^L_j))`; as printed, `A` carries an extra
`(σ^H_i − σ^L_i)²` in its denominator and `B` lacks `1/(σ^H_j − σ^L_j)`, which makes the printed identity
for `δ*_i` false. -/
theorem partials_own {n : ℕ} (M : Params n) (hS : M.Standing) (hβ : NoTechCoupling M)
    (hI : Interior M) (i : Fin n) :
    let d := M.sH i - M.sL i
    let A := (1 - M.c i) * (M.VH i - M.VL i) / M.r * M.P⁻¹ i i
    let B := ∑ j ∈ Finset.univ.erase i,
      (1 - M.c j) * (M.VH j - M.VL j) / (M.r * (M.sH j - M.sL j)) * M.P⁻¹ j i
    HasDerivAt (fun t => optEffort (withC M i t) i)
        (-(M.VH i - M.VL i) / (M.r * d ^ 2) * M.P⁻¹ i i) (M.c i) ∧
      -(M.VH i - M.VL i) / (M.r * d ^ 2) * M.P⁻¹ i i < 0 ∧
      HasDerivAt (fun t => optEffort (withVH M i t) i)
        ((1 - M.c i) / (M.r * d ^ 2) * M.P⁻¹ i i) (M.VH i) ∧
      0 < (1 - M.c i) / (M.r * d ^ 2) * M.P⁻¹ i i ∧
      0 < A ∧
      optEffort M i = 1 / d * (A / d + B - M.sL i) ∧
      HasDerivAt (fun t => optEffort (withSH M i t) i)
        (-(2 * A + (B - M.sL i) * d) / d ^ 3) (M.sH i) := by sorry

end HolisticService.Effort
