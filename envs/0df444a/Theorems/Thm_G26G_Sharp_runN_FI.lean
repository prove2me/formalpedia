-- Prove2me | Theorems.Thm_G26G_Sharp_runN_FI
-- name    : G26G.Sharp.runN_FI
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-18T00:30:31.356906+00:00
-- url     : https://prove2.me/theorems/f9623758-e096-494b-a73f-6d98768b1516
-- title:
--   The normalized remaining-budget field on the cone body D_θ satisfies the field interface while the reference is a*
-- statement:
--   **Setting.** $\mathcal A\subseteq\mathbb R^d$ is a compact action set spanning $\mathbb R^d$, $\mathcal B\subseteq\mathcal A$ is a compact generator ($\mathcal A\subseteq\mathcal K:=\operatorname{Conv}\mathcal B$), $e:\mathbb N\to\mathbb Q^d$ is the direction enumeration, and $R$ is a GIA-FTRL run of $T$ rounds (`IsGIAFTRLRun`) with cumulative loss estimate $S_n=\sum_{j<n}\hat\theta_j$, run filtration $(\mathcal G_n)$, learning rate $\beta_n=16d+\sqrt n$ (`gbeta`) and magnitude constant $B=2^{36}(d+1)$ (`gB`). The filtration used below is $\mathcal F_n=\mathcal G_n$ for $n<T$ and $\mathcal F_T=\mathcal F$ (`Fx`). The standing hypotheses `Sharp` hold: $\mathcal A$ lies in the unit ball, $k=\dim\mathcal K\ge1$, $\|\theta\|_{\mathcal A}\le1$, $a^*\in\mathcal A$ is the unique minimizer of $a\mapsto a^\top\theta$ on $\mathcal A$, and the instance is sharp with modulus $\varsigma>0$ (`H.sig`): $\Delta(a)=(a-a^*)^\top\theta\ge\varsigma\|a-a^*\|_{\mathcal S}$ on $\mathcal K$. The corruption is bounded by $C$: $\sum_{t<T}\|\theta_t-\theta\|_{\mathcal A}\le C$ a.s. (`IsCorruptedG`). The projective body is $U_\theta=\overline{\{\Delta(a)^{-1}(a-a^*):a\in\mathcal K\setminus\{a^*\}\}}$ and the cone body is $D_\theta=\{\lambda u:\lambda\in[0,1],u\in U_\theta\}$; $\Lambda=\varsigma^{-1}$, $A_n=\sum_{j<n}\|\theta_j-\theta\|_{\mathcal A}$, and $j^*$ is the index of $a^*$ among the reference atoms (`js`).
--
--   Assume $e$ is surjective and fix $m$. On the cone body $D_\theta$ consider the normalized shifted field
--   $$
--   W^u_n(u)=u^\top S_n-\Lambda\,(C-A_n)\qquad(u\in D_\theta),
--   $$
--   and the alive events $J_n=\{\text{the reference was strictly }a^*\text{ at every round of }[m,n]\}$ (`JN`). Then $W^u$ satisfies the field interface on $D_\theta$ from $m_0=m$ on, with budgets $\kappa_b\beta_{n+1}$ where $\kappa_b=\varsigma^{-2}+\varsigma^{-1}+1$, $B=2^{36}(d+1)$, and drift range $[0,1+4\varsigma^{-1}]$.
--
--   While the reference is $a^*$, Lemma G.17 transfers the homogeneous constraints on $\mathcal K-a^*$ to $D_\theta$, giving the magnitude and variance budgets with $\beta'_s=\Lambda^2\beta_s$. The conditional drift is $\theta^\top u+e_s(u)$ with $|e_s(u)|\le\Lambda\kappa_s$, compensated by the shift $\Lambda(A_{n+1}-A_n)$ as in (G.569)–(G.571).
--
--   **Formalization Note** The shift is `cN 𝒜 R θ H.sig⁻¹ C`; rounds are 0-based.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Appendix G, Lemma G.17 (p.154) and Lemma G.28, (G.569)–(G.571) (p.178)

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL
import Definitions.Def_IAFTRL_G26_body
import Definitions.Def_IAFTRL_G26_run
import Definitions.Def_IAFTRL_G26_window

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix
open G26G
open G26 G26R
variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}
open G26G.Sharp
variable (H : Sharp 𝒜 ℬ θ astar)
include H

theorem G26G.Sharp.runN_FI (he : Function.Surjective e) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {C : ℝ}
    (hC : 0 ≤ C) (hcor : IsCorruptedG P 𝒜 θ C T R) (m : ℕ) :
    FI (DT ℬ θ astar) P (Fx R T) T R.cumEst (cN 𝒜 R θ H.sig⁻¹ C) (JN ℬ e (js ℬ e astar) R m)
      (fun n => H.kb * gbeta d (n + 1)) (gB d) 0 (1 + 4 * H.sig⁻¹) m := by sorry
