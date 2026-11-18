-- Prove2me | Theorems.Thm_G26G_Sharp_runF_SI
-- name    : G26G.Sharp.runF_SI
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-18T00:30:13.06826+00:00
-- url     : https://prove2.me/theorems/649747e0-118c-4dbe-837a-34c8f3b4a001
-- title:
--   The compensated per-action variable satisfies the scalar interface while the remaining-budget field has not crossed
-- statement:
--   **Setting.** $\mathcal A\subseteq\mathbb R^d$ is a compact action set spanning $\mathbb R^d$, $\mathcal B\subseteq\mathcal A$ is a compact generator ($\mathcal A\subseteq\mathcal K:=\operatorname{Conv}\mathcal B$), $e:\mathbb N\to\mathbb Q^d$ is the direction enumeration, and $R$ is a GIA-FTRL run of $T$ rounds (`IsGIAFTRLRun`) with cumulative loss estimate $S_n=\sum_{j<n}\hat\theta_j$, run filtration $(\mathcal G_n)$, learning rate $\beta_n=16d+\sqrt n$ (`gbeta`) and magnitude constant $B=2^{36}(d+1)$ (`gB`). The filtration used below is $\mathcal F_n=\mathcal G_n$ for $n<T$ and $\mathcal F_T=\mathcal F$ (`Fx`). The standing hypotheses `Sharp` hold: $\mathcal A$ lies in the unit ball, $k=\dim\mathcal K\ge1$, $\|\theta\|_{\mathcal A}\le1$, $a^*\in\mathcal A$ is the unique minimizer of $a\mapsto a^\top\theta$ on $\mathcal A$, and the instance is sharp with modulus $\varsigma>0$ (`H.sig`): $\Delta(a)=(a-a^*)^\top\theta\ge\varsigma\|a-a^*\|_{\mathcal S}$ on $\mathcal K$. The corruption is bounded by $C$: $\sum_{t<T}\|\theta_t-\theta\|_{\mathcal A}\le C$ a.s. (`IsCorruptedG`). The projective body is $U_\theta=\overline{\{\Delta(a)^{-1}(a-a^*):a\in\mathcal K\setminus\{a^*\}\}}$ and the cone body is $D_\theta=\{\lambda u:\lambda\in[0,1],u\in U_\theta\}$; $\Lambda=\varsigma^{-1}$, $A_n=\sum_{j<n}\|\theta_j-\theta\|_{\mathcal A}$, and $j^*$ is the index of $a^*$ among the reference atoms (`js`).
--
--   Fix $a\in\mathcal K$ and a buffer sequence $\tau$ with $\tau_n>0$, $\tau_n\le\tau_{n+1}\le\tau_n+1$, an interval end $N\le T$, a start $m_0$, and assume $B(\beta_{n+1}+3)\le\tau_n$ for $n\ge m_0$. Consider the compensated variable
--   $$
--   Y^F_n(a)=(a-a^*)^\top S_n-E_n(a-a^*)+2C+2\tau_n,\qquad E_n(w)=\sum_{j<n}w^\top(\theta_j-\theta),
--   $$
--   and the alive events $I^W_n=\{\max_{\mathcal K}(-W_j)\le\tau_j\text{ for all }m_0\le j\le n\}$ (`IW`), where $W$ is the remaining-budget field of Lemma G.30. Then $\mathrm{SI}(m_0,N)$ holds for $(Y^F(a),I^W)$ with thresholds $\tau_n$, budgets $\beta_{n+1}$ and $B=2^{36}(d+1)$.
--
--   On $I^W_n$ one has $Y^F_n(a)\ge\tau_n$, because $W_n(a)\ge-\tau_n$ and the compensator differs from the shift by at most $2C$. The relative increment and conditional variance bounds come from Lemma G.10. These variables carry the far-reference estimate of Lemma G.29.
--
--   **Formalization Note** Rounds are 0-based.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Appendix G, Lemma G.29, (G.635)–(G.641) (p.184)

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

theorem G26G.Sharp.runF_SI (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {C : ℝ} (hcor : IsCorruptedG P 𝒜 θ C T R)
    {a : Fin d → ℝ} (ha : a ∈ Kset ℬ) {τ : ℕ → ℝ} (hτpos : ∀ n, 0 < τ n)
    (hτmono : ∀ n, τ n ≤ τ (n + 1)) (hδ : ∀ n, τ (n + 1) - τ n ≤ 1) {m0 N : ℕ} (hN : N ≤ T)
    (hτB : ∀ n, m0 ≤ n → gB d * (gbeta d (n + 1) + 3) ≤ τ n) :
    SI P (Fx R T) (YF R θ astar C τ a) (IW 𝒜 ℬ R θ astar C τ m0) m0 N τ
      (fun n => gbeta d (n + 1)) (gB d) := by sorry
