-- Prove2me | Theorems.Thm_G26G_Sharp_runN_SI
-- name    : G26G.Sharp.runN_SI
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-18T00:30:54.563467+00:00
-- url     : https://prove2.me/theorems/7e7c2ee3-86dc-4d0c-829c-6d0e44f2452c
-- title:
--   The compensated normalized variable satisfies the scalar interface on the alive window
-- statement:
--   **Setting.** $\mathcal A\subseteq\mathbb R^d$ is a compact action set spanning $\mathbb R^d$, $\mathcal B\subseteq\mathcal A$ is a compact generator ($\mathcal A\subseteq\mathcal K:=\operatorname{Conv}\mathcal B$), $e:\mathbb N\to\mathbb Q^d$ is the direction enumeration, and $R$ is a GIA-FTRL run of $T$ rounds (`IsGIAFTRLRun`) with cumulative loss estimate $S_n=\sum_{j<n}\hat\theta_j$, run filtration $(\mathcal G_n)$, learning rate $\beta_n=16d+\sqrt n$ (`gbeta`) and magnitude constant $B=2^{36}(d+1)$ (`gB`). The filtration used below is $\mathcal F_n=\mathcal G_n$ for $n<T$ and $\mathcal F_T=\mathcal F$ (`Fx`). The standing hypotheses `Sharp` hold: $\mathcal A$ lies in the unit ball, $k=\dim\mathcal K\ge1$, $\|\theta\|_{\mathcal A}\le1$, $a^*\in\mathcal A$ is the unique minimizer of $a\mapsto a^\top\theta$ on $\mathcal A$, and the instance is sharp with modulus $\varsigma>0$ (`H.sig`): $\Delta(a)=(a-a^*)^\top\theta\ge\varsigma\|a-a^*\|_{\mathcal S}$ on $\mathcal K$. The corruption is bounded by $C$: $\sum_{t<T}\|\theta_t-\theta\|_{\mathcal A}\le C$ a.s. (`IsCorruptedG`). The projective body is $U_\theta=\overline{\{\Delta(a)^{-1}(a-a^*):a\in\mathcal K\setminus\{a^*\}\}}$ and the cone body is $D_\theta=\{\lambda u:\lambda\in[0,1],u\in U_\theta\}$; $\Lambda=\varsigma^{-1}$, $A_n=\sum_{j<n}\|\theta_j-\theta\|_{\mathcal A}$, and $j^*$ is the index of $a^*$ among the reference atoms (`js`).
--
--   Assume $e$ is surjective. Fix $u\in D_\theta$, a buffer $\tau$ with $\tau_n>0$, $\tau_n\le\tau_{n+1}\le\tau_n+1$, $m$, $N\le T$, and assume $B(\beta_{n+1}\Lambda+2\Lambda+2)\le\tau_n$ for $n\ge m$. Consider
--   $$
--   Y^\dagger_n(u)=u^\top S_n-E_n(u)+\Lambda C+2\tau_n
--   $$
--   and the alive events $I_n$ (`IN`): the reference was strictly $a^*$ at every round of $[m,n]$, and $\max_{D_\theta}(-W^u_j)\le\tau_j$ for all $m\le j\le n$, as in (G.523). Then $\mathrm{SI}(m,N)$ holds for $(Y^\dagger(u),I)$ with thresholds $\tau_n$, budgets $\kappa_b\beta_{n+1}$ and $B=2^{36}(d+1)$.
--
--   These are the variables $Y^{\dagger,u}_s$ whose local moments (G.568) are bounded on the alive window. Lemma G.26 then contracts them uniformly over $U_\theta$.
--
--   **Formalization Note** Rounds are 0-based.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Appendix G, Lemma G.28, (G.595)–(G.601) (p.181)

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

theorem G26G.Sharp.runN_SI (he : Function.Surjective e) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {C : ℝ}
    (hcor : IsCorruptedG P 𝒜 θ C T R) {u : Fin d → ℝ} (hu : u ∈ DT ℬ θ astar) {τ : ℕ → ℝ}
    (hτpos : ∀ n, 0 < τ n) (hτmono : ∀ n, τ n ≤ τ (n + 1)) (hδ : ∀ n, τ (n + 1) - τ n ≤ 1)
    {m N : ℕ} (hN : N ≤ T)
    (hτB : ∀ n, m ≤ n → gB d * (gbeta d (n + 1) * H.sig⁻¹ + 2 * H.sig⁻¹ + 2) ≤ τ n) :
    SI P (Fx R T) (YN R θ H.sig⁻¹ C τ u) (IN 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C τ m) m N τ
      (fun n => H.kb * gbeta d (n + 1)) (gB d) := by sorry
