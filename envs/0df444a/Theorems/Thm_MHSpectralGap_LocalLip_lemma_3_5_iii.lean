-- Prove2me | Theorems.Thm_MHSpectralGap_LocalLip_lemma_3_5_iii
-- name    : MHSpectralGap.LocalLip.lemma_3_5_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:56:22.287116+00:00
-- url     : https://prove2.me/theorems/00c0cf99-cc55-4025-958c-290fab1a7cc5
-- title:
--   Lemma 3.5 (3), pp. 22–23 — the pCN step with a common noise contracts d̄ by (1 − 2δ)^{1/2} e^{η[−ρ(‖x‖∨‖y‖)+√(2δ)‖ξ‖+J]}
-- statement:
--   Let $H$ be a real inner product space, $\eta,\varepsilon>0$, $\delta\in(0,\tfrac12]$, $\rho=1-(1-2\delta)^{1/2}$, and let $\bar d$ and $J=\varepsilon\exp(-\eta((\|x\|\vee\|y\|-\varepsilon)\vee0))$ be as in (3.6) and Lemma 3.5. For $x,y,\xi\in H$ write
--
--   $$p_x=(1-2\delta)^{1/2}x+\sqrt{2\delta}\,\xi,\qquad p_y=(1-2\delta)^{1/2}y+\sqrt{2\delta}\,\xi$$
--
--   for the two pCN proposals driven by the same noise $\xi$. If $\bar d(x,y)<1$, then
--
--   $$\bar d(p_x,p_y)\le(1-2\delta)^{1/2}\exp\Bigl(\eta\bigl[-\rho(\|x\|\vee\|y\|)+\sqrt{2\delta}\,\|\xi\|+J\bigr]\Bigr)\,\bar d(x,y).$$
--
--   When both proposals are accepted, the distance therefore contracts unless the noise is large compared with $\rho(\|x\|\vee\|y\|)$; this is the "both accept" case of the contraction Lemma 3.6.
--
--   **Formalization Note** The statement printed in Lemma 3.5 (3) has the exponent $-\eta\rho[\|x\|\vee\|y\|+\eta(\|\sqrt{2\delta}\xi\|+J)]$, a typographical slip; the bound formalized is the last display of the proof on p. 23 ("which is precisely the required bound"), which is also the form used in the proof of Lemma 3.6 on p. 24.
-- source:
--   Hairer, Stuart and Vollmer, Spectral gaps for a Metropolis–Hastings algorithm in infinite dimensions, arXiv:1112.1392v4, p. 22, Lemma 3.5 (3), in the form of the last display of its proof, p. 23

import Mathlib
import Definitions.Def_MHSpectralGap_LocalLip_PathMetric
import Definitions.Def_MHSpectralGap_LocalLip_PCN

namespace MHSpectralGap.LocalLip

/-- Lemma 3.5 (3), in the form its proof derives (p. 23): with the pCN proposals
`p_x = (1 − 2δ)^{1/2} x + √(2δ) ξ`, `p_y = (1 − 2δ)^{1/2} y + √(2δ) ξ` driven by the same `ξ`,
for points with `d̄(x, y) < 1`,
`d̄(p_x, p_y) ≤ (1 − 2δ)^{1/2} exp(η[−ρ(‖x‖ ∨ ‖y‖) + √(2δ)‖ξ‖ + J]) d̄(x, y)`. -/
theorem lemma_3_5_iii {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) (δ : ℝ) (hδ : δ ∈ Set.Ioc 0 (1 / 2)) (x y ξ : H)
    (hd : dBarE η ε x y < 1) :
    dBarE η ε (Real.sqrt (1 - 2 * δ) • x + Real.sqrt (2 * δ) • ξ)
        (Real.sqrt (1 - 2 * δ) • y + Real.sqrt (2 * δ) • ξ) ≤
      ENNReal.ofReal (Real.sqrt (1 - 2 * δ) *
          Real.exp (η * (-(ρ δ * max ‖x‖ ‖y‖) + Real.sqrt (2 * δ) * ‖ξ‖ + Jlen η ε x y))) *
        dBarE η ε x y := by sorry

end MHSpectralGap.LocalLip
