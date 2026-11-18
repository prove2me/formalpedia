-- Prove2me | Theorems.Thm_G26G_Sharp_win_pos
-- name    : G26G.Sharp.win_pos
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-18T00:30:50.342591+00:00
-- url     : https://prove2.me/theorems/1cb337a2-cc7d-42ba-9cde-231b8f4d3a8e
-- title:
--   Local positive moment of the compensated normalized variable on the alive window
-- statement:
--   **Setting.** $\mathcal A\subseteq\mathbb R^d$ is a compact action set spanning $\mathbb R^d$, $\mathcal B\subseteq\mathcal A$ is a compact generator ($\mathcal A\subseteq\mathcal K:=\operatorname{Conv}\mathcal B$), $e:\mathbb N\to\mathbb Q^d$ is the direction enumeration, and $R$ is a GIA-FTRL run of $T$ rounds (`IsGIAFTRLRun`) with cumulative loss estimate $S_n=\sum_{j<n}\hat\theta_j$, run filtration $(\mathcal G_n)$, learning rate $\beta_n=16d+\sqrt n$ (`gbeta`) and magnitude constant $B=2^{36}(d+1)$ (`gB`). The filtration used below is $\mathcal F_n=\mathcal G_n$ for $n<T$ and $\mathcal F_T=\mathcal F$ (`Fx`). The standing hypotheses `Sharp` hold: $\mathcal A$ lies in the unit ball, $k=\dim\mathcal K\ge1$, $\|\theta\|_{\mathcal A}\le1$, $a^*\in\mathcal A$ is the unique minimizer of $a\mapsto a^\top\theta$ on $\mathcal A$, and the instance is sharp with modulus $\varsigma>0$ (`H.sig`): $\Delta(a)=(a-a^*)^\top\theta\ge\varsigma\|a-a^*\|_{\mathcal S}$ on $\mathcal K$. The corruption is bounded by $C$: $\sum_{t<T}\|\theta_t-\theta\|_{\mathcal A}\le C$ a.s. (`IsCorruptedG`). The projective body is $U_\theta=\overline{\{\Delta(a)^{-1}(a-a^*):a\in\mathcal K\setminus\{a^*\}\}}$ and the cone body is $D_\theta=\{\lambda u:\lambda\in[0,1],u\in U_\theta\}$; $\Lambda=\varsigma^{-1}$, $A_n=\sum_{j<n}\|\theta_j-\theta\|_{\mathcal A}$, and $j^*$ is the index of $a^*$ among the reference atoms (`js`).
--
--   Assume $e$ is surjective and $C\ge0$. Let $u\in U_\theta$, $z\ge0$, $m\le t<T$, $c_{Tw}\le(m+1)^{1/8}$, $\varsigma^{-1}C\le m+1$, and with $\xi=((m+1)/(t+1))^{1/8}$,
--   $$
--   z\le(t+1)\,\xi^{7},\qquad\big(2(\Lambda_1\max\{1,c_K\}+4)+16\big)\,\xi\le1 .
--   $$
--   Then, with $\tau_s=(s+1)^{7/8}+4z$, $Y^\dagger$, $I$ as in `runN_SI` and $P=4k$,
--   $$
--   \mathbb E\big[\mathbf 1_{I_t}\,(Y^\dagger_t(u))^{P}\big]\le\big(8(t+1)\big)^{P}.
--   $$
--
--   The starting value at $m$ is controlled by the absolute envelope of the normalized field and the projective extension constant $\Lambda_1$. The drift is at most $\theta^\top u+2\delta=1+2\delta$, and the scalar positive-moment estimate propagates this bound to time $t$. This is the positive part of (G.568).
--
--   **Formalization Note** Rounds are 0-based.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Appendix G, Lemma G.28, second estimate of (G.568) (p.178)

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
theorem G26G.Sharp.win_pos (he : Function.Surjective e) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {C : ℝ}
    (hC : 0 ≤ C) (hcor : IsCorruptedG P 𝒜 θ C T R) {u : Fin d → ℝ} (hu : u ∈ UT ℬ θ astar)
    {z : ℝ} (hz : 0 ≤ z) {m t : ℕ} (hmt : m ≤ t) (htT : t < T)
    (hmc : cTw d H.sig⁻¹ H.kb ≤ root8 ((m : ℝ) + 1)) (hlC : H.sig⁻¹ * C ≤ (m : ℝ) + 1)
    (hzt : z ≤ ((t : ℝ) + 1) * root8 (((m : ℝ) + 1) / ((t : ℝ) + 1)) ^ 7)
    (hξ : (2 * (Lam1 ℬ θ astar * max 1 (cK d) + 4) + 16) * root8 (((m : ℝ) + 1) / ((t : ℝ) + 1)) ≤ 1) :
    kpos P (YN R θ H.sig⁻¹ C (tauB z) u) (IN 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C (tauB z) m)
      (4 * kk d) t ≤ (8 * ((t : ℝ) + 1)) ^ (4 * kk d) := by sorry
