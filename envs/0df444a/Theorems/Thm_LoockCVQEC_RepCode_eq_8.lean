-- Prove2me | Theorems.Thm_LoockCVQEC_RepCode_eq_8
-- name    : LoockCVQEC.RepCode.eq_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:58:08.490062+00:00
-- url     : https://prove2.me/theorems/0f9fd5c4-517e-4f12-922b-4c3fce1292fd
-- title:
--   Eq. (8) — the decoded state: signal shifted by |S|x̄₂/√3, ancillas shifted to the syndrome of S
-- statement:
--   Encode the coherent input with two x-squeezed ancillas by the tritter, send each mode through the stochastic x-displacement channel (probability $\gamma$, size $\bar x_2$), and invert the tritter. The decoded state is
--   $$\begin{aligned}W_{\mathrm{dec}}={}&(1-\gamma)^3W_{\mathrm{in}}(x_1,p_1)W_{\mathrm{anc}}(x_2,p_2)W_{\mathrm{anc}}(x_3,p_3)\\
--   &+\gamma(1-\gamma)^2W_{\mathrm{in}}(x_1-\tfrac{\bar x_2}{\sqrt3},p_1)\,W_{\mathrm{anc}}(x_2-\sqrt{\tfrac23}\bar x_2,p_2)W_{\mathrm{anc}}(x_3,p_3)\\
--   &+\gamma(1-\gamma)^2W_{\mathrm{in}}(x_1-\tfrac{\bar x_2}{\sqrt3},p_1)\,W_{\mathrm{anc}}(x_2+\tfrac{\bar x_2}{\sqrt6},p_2)W_{\mathrm{anc}}(x_3-\tfrac{\bar x_2}{\sqrt2},p_3)\\
--   &+\gamma(1-\gamma)^2W_{\mathrm{in}}(x_1-\tfrac{\bar x_2}{\sqrt3},p_1)\,W_{\mathrm{anc}}(x_2+\tfrac{\bar x_2}{\sqrt6},p_2)W_{\mathrm{anc}}(x_3+\tfrac{\bar x_2}{\sqrt2},p_3)\\
--   &+\gamma^2(1-\gamma)W_{\mathrm{in}}(x_1-\tfrac{2\bar x_2}{\sqrt3},p_1)\,W_{\mathrm{anc}}(x_2-\tfrac{\bar x_2}{\sqrt6},p_2)W_{\mathrm{anc}}(x_3-\tfrac{\bar x_2}{\sqrt2},p_3)\\
--   &+\gamma^2(1-\gamma)W_{\mathrm{in}}(x_1-\tfrac{2\bar x_2}{\sqrt3},p_1)\,W_{\mathrm{anc}}(x_2-\tfrac{\bar x_2}{\sqrt6},p_2)W_{\mathrm{anc}}(x_3+\tfrac{\bar x_2}{\sqrt2},p_3)\\
--   &+\gamma^2(1-\gamma)W_{\mathrm{in}}(x_1-\tfrac{2\bar x_2}{\sqrt3},p_1)\,W_{\mathrm{anc}}(x_2+\sqrt{\tfrac23}\bar x_2,p_2)W_{\mathrm{anc}}(x_3,p_3)\\
--   &+\gamma^3W_{\mathrm{in}}(x_1-\sqrt3\,\bar x_2,p_1)\,W_{\mathrm{anc}}(x_2,p_2)W_{\mathrm{anc}}(x_3,p_3)\end{aligned}$$
--   for all $x,p\in\mathbb R^3$. The eight terms are, in order, no error, an error in channel 1, 2, 3, errors in channels $\{1,2\}$, $\{1,3\}$, $\{2,3\}$, and errors in all three.
--
--   After decoding, every error pattern leaves the signal mode a displaced copy of the input (by $|S|\bar x_2/\sqrt3$) and moves the two ancillas to a pattern-dependent point; this is what makes syndrome extraction possible.
--
--   **Formalization Note** The left-hand side is computed from the protocol (product state, tritter, three channels, inverse tritter). Lean index $0$ is the paper's mode 1.
--
--   Differences from the source:
--   - encoding: modes and channels numbered 1, 2, 3 → Fin 3, Lean index j − 1 for the paper's mode j; reason: Lean convention; same instances
--   - reading: the tritter is "a sequence of two beam splitters with transmittances 1 : 2 and 1 : 1"; its matrix is not printed → the orthogonal matrix D with rows (1,1,1)/√3, (√(2/3), −1/√6, −1/√6), (0, 1/√2, −1/√2); encode W ↦ W(Dx, Dp), decode W ↦ W(Dᵀx, Dᵀp); reason: this D reproduces Eq. (6) and every term, with signs, of Eq. (8) on the page
-- source:
--   van Loock, A note on quantum error correction with continuous variables, arXiv:0811.3616v1, pp. 2–3, Eq. (8)

import Mathlib
import Definitions.Def_LoockCVQEC_RepCode_Protocol

namespace LoockCVQEC.RepCode

open Real

theorem eq_8 (xb pb r γ d : ℝ) (x p : Fin 3 → ℝ) :
    decoded xb pb r γ d x p =
      (1 - γ) ^ 3 * inW xb pb (x 0) (p 0) * ancW r (x 1) (p 1) * ancW r (x 2) (p 2)
      + γ * (1 - γ) ^ 2 * inW xb pb (x 0 - 1 / √3 * d) (p 0)
          * ancW r (x 1 - √(2 / 3) * d) (p 1) * ancW r (x 2) (p 2)
      + γ * (1 - γ) ^ 2 * inW xb pb (x 0 - 1 / √3 * d) (p 0)
          * ancW r (x 1 + 1 / √6 * d) (p 1) * ancW r (x 2 - 1 / √2 * d) (p 2)
      + γ * (1 - γ) ^ 2 * inW xb pb (x 0 - 1 / √3 * d) (p 0)
          * ancW r (x 1 + 1 / √6 * d) (p 1) * ancW r (x 2 + 1 / √2 * d) (p 2)
      + γ ^ 2 * (1 - γ) * inW xb pb (x 0 - 2 / √3 * d) (p 0)
          * ancW r (x 1 - 1 / √6 * d) (p 1) * ancW r (x 2 - 1 / √2 * d) (p 2)
      + γ ^ 2 * (1 - γ) * inW xb pb (x 0 - 2 / √3 * d) (p 0)
          * ancW r (x 1 - 1 / √6 * d) (p 1) * ancW r (x 2 + 1 / √2 * d) (p 2)
      + γ ^ 2 * (1 - γ) * inW xb pb (x 0 - 2 / √3 * d) (p 0)
          * ancW r (x 1 + √(2 / 3) * d) (p 1) * ancW r (x 2) (p 2)
      + γ ^ 3 * inW xb pb (x 0 - √3 * d) (p 0) * ancW r (x 1) (p 1) * ancW r (x 2) (p 2) := by sorry

end LoockCVQEC.RepCode
