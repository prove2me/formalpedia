-- Prove2me | Theorems.Thm_G26G_Sharp_win_round
-- name    : G26G.Sharp.win_round
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-18T00:30:34.264616+00:00
-- url     : https://prove2.me/theorems/2dee4ee0-34a2-40e7-a67a-626981fab8f5
-- title:
--   Per-round failure bound of Lemma G.26: P(G_tᶜ) ≤ D_θ{(t+1)^{-2} + (H_C/(t+1))^2}
-- statement:
--   **Setting.** $\mathcal A\subseteq\mathbb R^d$ is a compact action set spanning $\mathbb R^d$, $\mathcal B\subseteq\mathcal A$ is a compact generator ($\mathcal A\subseteq\mathcal K:=\operatorname{Conv}\mathcal B$), $e:\mathbb N\to\mathbb Q^d$ is the direction enumeration, and $R$ is a GIA-FTRL run of $T$ rounds (`IsGIAFTRLRun`) with cumulative loss estimate $S_n=\sum_{j<n}\hat\theta_j$, run filtration $(\mathcal G_n)$, learning rate $\beta_n=16d+\sqrt n$ (`gbeta`) and magnitude constant $B=2^{36}(d+1)$ (`gB`). The filtration used below is $\mathcal F_n=\mathcal G_n$ for $n<T$ and $\mathcal F_T=\mathcal F$ (`Fx`). The standing hypotheses `Sharp` hold: $\mathcal A$ lies in the unit ball, $k=\dim\mathcal K\ge1$, $\|\theta\|_{\mathcal A}\le1$, $a^*\in\mathcal A$ is the unique minimizer of $a\mapsto a^\top\theta$ on $\mathcal A$, and the instance is sharp with modulus $\varsigma>0$ (`H.sig`): $\Delta(a)=(a-a^*)^\top\theta\ge\varsigma\|a-a^*\|_{\mathcal S}$ on $\mathcal K$. The corruption is bounded by $C$: $\sum_{t<T}\|\theta_t-\theta\|_{\mathcal A}\le C$ a.s. (`IsCorruptedG`). The projective body is $U_\theta=\overline{\{\Delta(a)^{-1}(a-a^*):a\in\mathcal K\setminus\{a^*\}\}}$ and the cone body is $D_\theta=\{\lambda u:\lambda\in[0,1],u\in U_\theta\}$; $\Lambda=\varsigma^{-1}$, $A_n=\sum_{j<n}\|\theta_j-\theta\|_{\mathcal A}$, and $j^*$ is the index of $a^*$ among the reference atoms (`js`).
--
--   Assume $e$ is surjective and $C\ge0$. For $t_0\le t<T$ (with $t_0$, $m=m_t$, $z=z_t$, $H_C$ as in `win_ok`), let
--   $$
--   G_t=I_t\cap\{0\le A_n\le C\ \forall n\le T\}\cap\Big\{\min_{u\in U_\theta}W^u_t(u)\ge4\tau_t\Big\}
--   $$
--   be the good event of Lemma G.26 (`Gev`), where $I_t$ is the alive event of (G.523) on the window $[m,t]$. Then
--   $$
--   \mathbb P(G_t^c)\le D_\theta\Big(\frac1{(t+1)^2}+\Big(\frac{H_C}{t+1}\Big)^2\Big),
--   $$
--   with $D_\theta$ (`H.Dθ he`) depending only on the instance.
--
--   The failure probability is split into reference errors on dyadic blocks (Lemma G.29), normalized negative crossings (Lemma G.28), and the contraction step on $U_\theta$ that compares $\min_{U_\theta}W^u_t$ with $4\tau_t$. This is the first estimate in (G.525). Summing it with weights $t^{-1/2}$ gives the weighted failure bound of Lemma G.26.
--
--   **Formalization Note** Rounds are 0-based.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Appendix G, Lemma G.26, first estimate of (G.525) (p.174)

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
theorem G26G.Sharp.win_round (he : Function.Surjective e) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {C : ℝ}
    (hC : 0 ≤ C) (hcor : IsCorruptedG P 𝒜 θ C T R) {t : ℕ} (htT : t < T)
    (ht0 : H.t0f he C ≤ t) :
    P.real (Gev 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C (zw (mw (H.M0 he) (Hcf C) t) t) T
        (mw (H.M0 he) (Hcf C) t) t)ᶜ ≤
      H.Dθ he * (1 / ((t : ℝ) + 1) ^ 2 + (Hcf C / ((t : ℝ) + 1)) ^ 2) := by sorry
