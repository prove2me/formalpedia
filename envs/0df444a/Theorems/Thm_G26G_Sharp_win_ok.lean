-- Prove2me | Theorems.Thm_G26G_Sharp_win_ok
-- name    : G26G.Sharp.win_ok
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-18T00:30:43.642868+00:00
-- url     : https://prove2.me/theorems/82c1fee4-1f12-46b2-aaec-484b44f5afac
-- title:
--   The window parameters of Definition G.8 satisfy all window hypotheses for t ≥ t₀
-- statement:
--   **Setting.** The standing hypotheses `Sharp` of the sharp corrupted instance hold (see `runN_FI`), and $e$ is surjective. Let $C\ge0$, $n_C=\lceil C\rceil+1$, $H_C=(n_C+1)\log(e(n_C+1))$, and for a round $t$ set
--   $$
--   m=\lceil M_0H_C\rceil+\lceil\sqrt{H_C(t+1)}\rceil,\qquad z=(t+1)\Big(\frac{m+1}{t+1}\Big)^{7/8},\qquad\tau_s=(s+1)^{7/8}+4z,
--   $$
--   where $M_0$ (`H.M0 he`) is an instance constant.
--
--   **Claim.** If $t\ge t_0=\lceil U_wH_C\rceil$ (`H.t0f he C`), then all of the following hold: $1\le m\le t$, $2(m+1)\le t+1$; $c_{Tw}\le(m+1)^{1/8}$; $\varsigma^{-1}C\le m+1$; $2S_{\rm ref}+2\le m$; $2^{21}(n_C+1)\log(e(n_C+1))\le m+1$; $0<z$ and $m+1\le z\le(t+1)((m+1)/(t+1))^{7/8}$; $\kappa_1((m+1)/(t+1))^{1/8}\le1$; $((m+1)/z)^8\le(m+1)/(t+1)$; $(t+1)/(m+1)\le m+1$; $\tau_t\le t+1$; and the tail bounds
--   $$
--   \Big(\frac{\tau_t}{t+1}\Big)^{16}\le2^{16}\Big(\frac1{(t+1)^2}+4^{16}\Big(\frac{m+1}{t+1}\Big)^4\Big),\qquad\Big(\frac{m+1}{t+1}\Big)^4\le16\big((M_0+3)^4+1\big)\Big(\frac{H_C}{t+1}\Big)^2,
--   $$
--   $$
--   \frac{(n_C+1)^4+1}{(m+1)^4}\le\Big(\frac{H_C}{t+1}\Big)^2+\frac1{(t+1)^2},\qquad\frac1{(m+1)^4}\le\frac1{(t+1)^2}.
--   $$
--
--   These are the comparisons "$m\ge N$, $m\le t/2$, $m\ge\Lambda C$, $\tau_s\ge4\Lambda C$, $\tau_t\le t$" of Definition G.8, made explicit, together with the conversions of the window error terms into $(t+1)^{-2}+(H_C/(t+1))^2$.
--
--   **Formalization Note** Rounds are 0-based; the statement uses `let` for $H_C$, $m$, $z$.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Appendix G, Definition G.8, (G.522) and the comparisons stated after it (p.173)

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL
import Definitions.Def_IAFTRL_G26_body
import Definitions.Def_IAFTRL_G26_run
import Definitions.Def_IAFTRL_G26_window

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11
open G26G
open G26 G26R
variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}
open G26G.Sharp
variable (H : Sharp 𝒜 ℬ θ astar) (he : Function.Surjective e)
include H he

theorem G26G.Sharp.win_ok {C : ℝ} (hC : 0 ≤ C) {t : ℕ} (ht0 : H.t0f he C ≤ t) :
    let Hc := Hcf C
    let m := mw (H.M0 he) Hc t
    let z := zw m t
    1 ≤ m ∧ m ≤ t ∧ 2 * ((m : ℝ) + 1) ≤ (t : ℝ) + 1 ∧
    cTw d H.sig⁻¹ H.kb ≤ root8 ((m : ℝ) + 1) ∧ H.sig⁻¹ * C ≤ (m : ℝ) + 1 ∧
    2 * H.Sref he + 2 ≤ m ∧
    2 ^ 21 * (((nCf C : ℝ) + 1) * Real.log (Real.exp 1 * ((nCf C : ℝ) + 1))) ≤ (m : ℝ) + 1 ∧
    0 < z ∧ (m : ℝ) + 1 ≤ z ∧
    z ≤ ((t : ℝ) + 1) * root8 (((m : ℝ) + 1) / ((t : ℝ) + 1)) ^ 7 ∧
    H.κ1 * root8 (((m : ℝ) + 1) / ((t : ℝ) + 1)) ≤ 1 ∧
    (((m : ℝ) + 1) / z) ^ 8 ≤ ((m : ℝ) + 1) / ((t : ℝ) + 1) ∧
    ((t : ℝ) + 1) / ((m : ℝ) + 1) ≤ (m : ℝ) + 1 ∧
    tauB z t ≤ (t : ℝ) + 1 ∧
    (tauB z t / ((t : ℝ) + 1)) ^ 16 ≤
      2 ^ 16 * (1 / ((t : ℝ) + 1) ^ 2 + 4 ^ 16 * (((m : ℝ) + 1) / ((t : ℝ) + 1)) ^ 4) ∧
    (((m : ℝ) + 1) / ((t : ℝ) + 1)) ^ 4 ≤
      16 * (((H.M0 he : ℝ) + 3) ^ 4 + 1) * (Hc / ((t : ℝ) + 1)) ^ 2 ∧
    (((nCf C : ℝ) + 1) ^ 4 + 1) / ((m : ℝ) + 1) ^ 4 ≤
      (Hc / ((t : ℝ) + 1)) ^ 2 + 1 / ((t : ℝ) + 1) ^ 2 ∧
    1 / ((m : ℝ) + 1) ^ 4 ≤ 1 / ((t : ℝ) + 1) ^ 2 := by sorry
