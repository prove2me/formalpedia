-- Prove2me | Theorems.Thm_MHSpectralGap_LocalLip_lemma_3_5_i
-- name    : MHSpectralGap.LocalLip.lemma_3_5_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:55:01.493408+00:00
-- url     : https://prove2.me/theorems/13190483-f434-4d40-9e91-7c3b84050332
-- title:
--   Lemma 3.5 (1), p. 22 — a unit-speed path of weighted length below 1 has length T ≤ J ≤ ε
-- statement:
--   Let $H$ be a real inner product space, $\eta,\varepsilon>0$, $x,y\in H$, $T\ge0$, and let $\psi\in\mathsf A(T,x,y)$ be a $C^1$ unit-speed path from $x$ to $y$ (see the path-metric definition). If
--
--   $$\frac1\varepsilon\int_0^T\exp(\eta\|\psi(t)\|)\,dt<1,$$
--
--   then
--
--   $$T\le J:=\varepsilon\exp\bigl(-\eta\,((\|x\|\vee\|y\|-\varepsilon)\vee0)\bigr)\le\varepsilon.$$
--
--   A path that is short for the weighted length $\bar d$ is therefore short in the ordinary sense, and shorter still far from the origin; this is how Lemma 3.5 compares $\bar d$ with the norm distance.
--
--   **Formalization Note** The paper writes $\exp(-\eta(\|x\|\vee\|y\|-\varepsilon)\vee0)$; the "$\vee0$" is applied to $\|x\|\vee\|y\|-\varepsilon$, as the proof's $Te^{\eta(\|x\|\vee\|y\|-\varepsilon)\vee0}$ shows.
-- source:
--   Hairer, Stuart and Vollmer, Spectral gaps for a Metropolis–Hastings algorithm in infinite dimensions, arXiv:1112.1392v4, p. 22, Lemma 3.5 (1)

import Mathlib
import Definitions.Def_MHSpectralGap_LocalLip_PathMetric

namespace MHSpectralGap.LocalLip

/-- Lemma 3.5 (1), p. 22: for a unit-speed path `ψ ∈ A(T, x, y)`,
`(1/ε) ∫_0^T exp(η‖ψ‖) dt < 1` implies `T ≤ J := ε exp(−η((‖x‖ ∨ ‖y‖ − ε) ∨ 0)) ≤ ε`. -/
theorem lemma_3_5_i {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) (x y : H) (T : ℝ) (hT : 0 ≤ T) (ψ : ℝ → H)
    (hψ : ψ ∈ pathSet x y T)
    (hcost : (1 / ε) * ∫ t in (0)..T, Real.exp (η * ‖ψ t‖) < 1) :
    T ≤ Jlen η ε x y ∧ Jlen η ε x y ≤ ε := by sorry

end MHSpectralGap.LocalLip
