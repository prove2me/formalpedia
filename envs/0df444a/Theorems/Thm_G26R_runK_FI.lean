-- Prove2me | Theorems.Thm_G26R_runK_FI
-- name    : G26R.runK_FI
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-18T00:30:23.897146+00:00
-- url     : https://prove2.me/theorems/7a81d377-6f8b-4674-a645-1226c3cc63b1
-- title:
--   The loss-difference field of a GIA-FTRL run on K satisfies the field interface
-- statement:
--   **Setting.** $\mathcal A\subseteq\mathbb R^d$ is a compact action set spanning $\mathbb R^d$, $\mathcal B\subseteq\mathcal A$ is a compact generator ($\mathcal A\subseteq\mathcal K:=\operatorname{Conv}\mathcal B$), $e:\mathbb N\to\mathbb Q^d$ is the direction enumeration, and $R$ is a GIA-FTRL run of $T$ rounds (`IsGIAFTRLRun`) with cumulative loss estimate $S_n=\sum_{j<n}\hat\theta_j$, run filtration $(\mathcal G_n)$, learning rate $\beta_n=16d+\sqrt n$ (`gbeta`) and magnitude constant $B=2^{36}(d+1)$ (`gB`). The filtration used below is $\mathcal F_n=\mathcal G_n$ for $n<T$ and $\mathcal F_T=\mathcal F$ (`Fx`).
--
--   Assume $d\ge1$, $\mathcal A,\mathcal B$ compact, $\mathcal B$ a generator of $\mathcal A$, $\operatorname{span}\mathcal A=\mathbb R^d$, and let $a^*\in\mathcal K$. Consider the affine field on $\mathcal K$
--   $$
--   X_n(a)=(a-a^*)^\top S_n=a^\top S_n-a^{*\top}S_n\qquad(a\in\mathcal K).
--   $$
--   Then $X$ satisfies the field interface on $D=\mathcal K$ with alive events $J_n=\Omega$, budgets $\beta_{n+1}=16d+\sqrt{n+1}$ and $B=2^{36}(d+1)$, drift range $[-2,2]$, and start $m_0=0$:
--   $$
--   \mathrm{FI}\big(\mathcal K;\ (\mathcal F_n);\ T;\ V_n=S_n,\ c_n=-a^{*\top}S_n;\ J_n=\Omega;\ \beta_{n+1};\ B;\ -2,\ 2;\ 0\big).
--   $$
--
--   The conditional mean of an increment is $(a-a^*)^\top\theta_n\in[-2,2]$ (unbiased estimates, actions and losses in the unit ball), and the magnitude and second-moment budgets are the universal bounds (G.153)–(G.154) of Lemma G.10. This yields the absolute envelopes of Lemma G.15.
--
--   **Formalization Note** Rounds are 0-based: $S_n$ sums the estimates of run rounds $j<n$.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Appendix G, Lemma G.10, (G.153)–(G.154) (p.139), as used in Lemma G.15 (p.152) and Lemma G.30 (p.188)

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL
import Definitions.Def_IAFTRL_G26_body
import Definitions.Def_IAFTRL_G26_run
import Definitions.Def_IAFTRL_G26_window

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix
open G26R
open G26
variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

theorem G26R.runK_FI (hd : 1 ≤ d) (h𝒜 : IsCompact 𝒜) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ)
    (hspan : Submodule.span ℝ 𝒜 = ⊤) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {astar : Fin d → ℝ}
    (haK : astar ∈ Kset ℬ) :
    FI (Kset ℬ) P (Fx R T) T R.cumEst (fun n ω => -(astar ⬝ᵥ R.cumEst n ω)) (fun _ => univ)
      (fun n => gbeta d (n + 1)) (gB d) (-2) 2 0 := by sorry
