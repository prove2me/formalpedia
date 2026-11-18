-- Prove2me | Theorems.Thm_G26G_Sharp_cross_window
-- name    : G26G.Sharp.cross_window
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-18T00:31:09.343795+00:00
-- url     : https://prove2.me/theorems/bdefbdee-9b91-4cb7-84a5-852d3c77434b
-- title:
--   Normalized negative crossings on the alive window (dyadic blocks)
-- statement:
--   **Setting.** $\mathcal A\subseteq\mathbb R^d$ is a compact action set spanning $\mathbb R^d$, $\mathcal B\subseteq\mathcal A$ is a compact generator ($\mathcal A\subseteq\mathcal K:=\operatorname{Conv}\mathcal B$), $e:\mathbb N\to\mathbb Q^d$ is the direction enumeration, and $R$ is a GIA-FTRL run of $T$ rounds (`IsGIAFTRLRun`) with cumulative loss estimate $S_n=\sum_{j<n}\hat\theta_j$, run filtration $(\mathcal G_n)$, learning rate $\beta_n=16d+\sqrt n$ (`gbeta`) and magnitude constant $B=2^{36}(d+1)$ (`gB`). The filtration used below is $\mathcal F_n=\mathcal G_n$ for $n<T$ and $\mathcal F_T=\mathcal F$ (`Fx`). The standing hypotheses `Sharp` hold: $\mathcal A$ lies in the unit ball, $k=\dim\mathcal K\ge1$, $\|\theta\|_{\mathcal A}\le1$, $a^*\in\mathcal A$ is the unique minimizer of $a\mapsto a^\top\theta$ on $\mathcal A$, and the instance is sharp with modulus $\varsigma>0$ (`H.sig`): $\Delta(a)=(a-a^*)^\top\theta\ge\varsigma\|a-a^*\|_{\mathcal S}$ on $\mathcal K$. The corruption is bounded by $C$: $\sum_{t<T}\|\theta_t-\theta\|_{\mathcal A}\le C$ a.s. (`IsCorruptedG`). The projective body is $U_\theta=\overline{\{\Delta(a)^{-1}(a-a^*):a\in\mathcal K\setminus\{a^*\}\}}$ and the cone body is $D_\theta=\{\lambda u:\lambda\in[0,1],u\in U_\theta\}$; $\Lambda=\varsigma^{-1}$, $A_n=\sum_{j<n}\|\theta_j-\theta\|_{\mathcal A}$, and $j^*$ is the index of $a^*$ among the reference atoms (`js`).
--
--   Assume $e$ is surjective and $C\ge0$. Let $1\le m\le t<T$ and $z>0$ with
--   $$
--   \Big(\frac{m+1}{z}\Big)^8\le\frac{m+1}{t+1},\qquad\varsigma^{-1}C\le m+1,\qquad\frac{t+1}{m+1}\le m+1 .
--   $$
--   Then the probability that, at some round $s\in[m,t]$ at which the reference has been $a^*$ since $m$, the normalized field has a negative crossing $\max_{D_\theta}(-W^u_s)>\tau_s=(s+1)^{7/8}+4z$, satisfies
--   $$
--   \mathbb P\big(\exists s\in[m,t]:\ \omega\in J_s,\ \tau_s<\max_{D_\theta}(-W^u_s)\big)\le2c_{X1}\Big(\frac{m+1}{t+1}\Big)^4+\frac{18\,c_{XB}}{(m+1)^4},
--   $$
--   with instance constants $c_{X1}$, $c_{XB}$ (`H.cX1`, `H.cXB`).
--
--   The proof splits $[m,t]$ into dyadic blocks $[2^im,2^{i+1}m]$ and applies the crossing envelope to the normalized field on each block, with the projective extension (G.306) controlling the absolute envelope. This is the crossing part of the alive-window bound (G.567).
--
--   **Formalization Note** Rounds are 0-based.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Appendix G, Lemma G.28, (G.567) (p.178), crossing part

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

omit he in
theorem G26G.Sharp.cross_window (he : Function.Surjective e) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {C : ℝ}
    (hC : 0 ≤ C) (hcor : IsCorruptedG P 𝒜 θ C T R) {m t : ℕ} {z : ℝ} (hz0 : 0 < z)
    (hm : 1 ≤ m) (hmt : m ≤ t) (htT : t < T)
    (hzx : (((m : ℝ) + 1) / z) ^ 8 ≤ ((m : ℝ) + 1) / ((t : ℝ) + 1))
    (hlC : H.sig⁻¹ * C ≤ (m : ℝ) + 1) (htm : ((t : ℝ) + 1) / ((m : ℝ) + 1) ≤ (m : ℝ) + 1) :
    P.real {ω | ∃ s, m ≤ s ∧ s ≤ t ∧ ω ∈ JN ℬ e (js ℬ e astar) R m s ∧
        tauB z s < negMax (DT ℬ θ astar) (R.cumEst s ω) (cN 𝒜 R θ H.sig⁻¹ C s ω)} ≤
      2 * H.cX1 * (((m : ℝ) + 1) / ((t : ℝ) + 1)) ^ 4 + 18 * H.cXB / ((m : ℝ) + 1) ^ 4 := by sorry
