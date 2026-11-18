-- Prove2me | Theorems.Thm_G26R_runW_FI
-- name    : G26R.runW_FI
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-18T00:30:34.741387+00:00
-- url     : https://prove2.me/theorems/b5c9a08c-2f84-4574-a07a-9f6d7fb4bb82
-- title:
--   The remaining-budget shifted field of a corrupted GIA-FTRL run satisfies the field interface with nonnegative drift
-- statement:
--   **Setting.** $\mathcal A\subseteq\mathbb R^d$ is a compact action set spanning $\mathbb R^d$, $\mathcal B\subseteq\mathcal A$ is a compact generator ($\mathcal A\subseteq\mathcal K:=\operatorname{Conv}\mathcal B$), $e:\mathbb N\to\mathbb Q^d$ is the direction enumeration, and $R$ is a GIA-FTRL run of $T$ rounds (`IsGIAFTRLRun`) with cumulative loss estimate $S_n=\sum_{j<n}\hat\theta_j$, run filtration $(\mathcal G_n)$, learning rate $\beta_n=16d+\sqrt n$ (`gbeta`) and magnitude constant $B=2^{36}(d+1)$ (`gB`). The filtration used below is $\mathcal F_n=\mathcal G_n$ for $n<T$ and $\mathcal F_T=\mathcal F$ (`Fx`).
--
--   Assume $d\ge1$, $\mathcal A,\mathcal B$ compact, $\mathcal B$ a generator of $\mathcal A$, $\operatorname{span}\mathcal A=\mathbb R^d$, $a^*\in\mathcal K$ minimizes $a\mapsto a^\top\theta$ on $\mathcal K$, $C\ge0$, and the run is $C$-corrupted around $\theta$: $\|\theta\|_{\mathcal A}\le1$ and $\sum_{t<T}\|\theta_t-\theta\|_{\mathcal A}\le C$ a.s. With $A_n=\sum_{j<n}\|\theta_j-\theta\|_{\mathcal A}$, the shifted field
--   $$
--   W_n(a)=(a-a^*)^\top S_n-2\,(C-A_n)\qquad(a\in\mathcal K)
--   $$
--   satisfies the field interface on $\mathcal K$ with $J_n=\Omega$, budgets $\beta_{n+1}$ and $B=2^{36}(d+1)$, drift range $[0,6]$, and $m_0=0$.
--
--   The shift by twice the unused corruption budget makes the drift nonnegative: $(a-a^*)^\top\theta_n\ge\Delta(a)-|(a-a^*)^\top(\theta_n-\theta)|$ and the second term is compensated by $2(A_{n+1}-A_n)$. This is the field whose negative maximum $Q_s=\max_{\mathcal K}(-W_s)$ is controlled in (G.678).
--
--   **Formalization Note** The shift is `cW 𝒜 R θ astar C`; rounds are 0-based.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Appendix G, Lemma G.30 (p.188), the field W_s(a) = X_s(a) − 2(C − A_s)

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

theorem G26R.runW_FI (hd : 1 ≤ d) (h𝒜 : IsCompact 𝒜) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ)
    (hspan : Submodule.span ℝ 𝒜 = ⊤) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {astar θ : Fin d → ℝ}
    (haK : astar ∈ Kset ℬ) (hopt : ∀ u ∈ Kset ℬ, astar ⬝ᵥ θ ≤ u ⬝ᵥ θ) {C : ℝ} (hC : 0 ≤ C)
    (hcor : IsCorruptedG P 𝒜 θ C T R) :
    FI (Kset ℬ) P (Fx R T) T R.cumEst (cW 𝒜 R θ astar C) (fun _ => univ)
      (fun n => gbeta d (n + 1)) (gB d) 0 6 0 := by sorry
