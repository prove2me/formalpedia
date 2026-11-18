-- Prove2me | Theorems.Thm_G26G_Sharp_far_prob
-- name    : G26G.Sharp.far_prob
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-18T00:30:40.14368+00:00
-- url     : https://prove2.me/theorems/4cd67127-167f-46f0-a090-54c6cf9f4e56
-- title:
--   Far reference errors on a block: some far action has a small compensated cumulative loss difference
-- statement:
--   **Setting.** $\mathcal A\subseteq\mathbb R^d$ is a compact action set spanning $\mathbb R^d$, $\mathcal B\subseteq\mathcal A$ is a compact generator ($\mathcal A\subseteq\mathcal K:=\operatorname{Conv}\mathcal B$), $e:\mathbb N\to\mathbb Q^d$ is the direction enumeration, and $R$ is a GIA-FTRL run of $T$ rounds (`IsGIAFTRLRun`) with cumulative loss estimate $S_n=\sum_{j<n}\hat\theta_j$, run filtration $(\mathcal G_n)$, learning rate $\beta_n=16d+\sqrt n$ (`gbeta`) and magnitude constant $B=2^{36}(d+1)$ (`gB`). The filtration used below is $\mathcal F_n=\mathcal G_n$ for $n<T$ and $\mathcal F_T=\mathcal F$ (`Fx`). The standing hypotheses `Sharp` hold: $\mathcal A$ lies in the unit ball, $k=\dim\mathcal K\ge1$, $\|\theta\|_{\mathcal A}\le1$, $a^*\in\mathcal A$ is the unique minimizer of $a\mapsto a^\top\theta$ on $\mathcal A$, and the instance is sharp with modulus $\varsigma>0$ (`H.sig`): $\Delta(a)=(a-a^*)^\top\theta\ge\varsigma\|a-a^*\|_{\mathcal S}$ on $\mathcal K$. The corruption is bounded by $C$: $\sum_{t<T}\|\theta_t-\theta\|_{\mathcal A}\le C$ a.s. (`IsCorruptedG`). The projective body is $U_\theta=\overline{\{\Delta(a)^{-1}(a-a^*):a\in\mathcal K\setminus\{a^*\}\}}$ and the cone body is $D_\theta=\{\lambda u:\lambda\in[0,1],u\in U_\theta\}$; $\Lambda=\varsigma^{-1}$, $A_n=\sum_{j<n}\|\theta_j-\theta\|_{\mathcal A}$, and $j^*$ is the index of $a^*$ among the reference atoms (`js`).
--
--   Let $C\ge0$, $P=4k$ with $k=1024(d+1)$, and let $\tau$ be a positive nondecreasing buffer with $\tau_{n+1}-\tau_n\le1$. Let $m_0\le u$ with $2u\le T$, $2(m_0+1)\le u+1$, $P+1\le2(m_0+1)$, $B(\beta_{n+1}+3)\le\tau_n$ for $n\ge m_0$, $2(P+1)\le\tau_{m_0}$, and $40(P+1)\beta_{n+1}(n+1)\le\tau_{m_0}^2$ for $m_0\le n<2u$. Let $\varepsilon>0$, $h$ with $h+4C\le2\tau_{2u}$, and $\rho\ge\max\{4\tau_{2u},2(4C+2\tau_{2u})\}$. With $D_\varepsilon=\{a\in\mathcal K:\Delta(a)\ge\varepsilon\}$ (`Dfar`),
--   $$
--   \mathbb P\big(\exists s\in[u,2u],\ \exists a\in D_\varepsilon:\ (a-a^*)^\top S_s\le h\big)\le\mathbb P\big((I^W_{2u})^c\big)+\frac{2^{P}c_K(2u+1)^{P}}{\rho^{P}}+\big(8\tau_{2u}\big)^{P}\Big(\frac{\rho}{4\tau_{2u}}\Big)^{d}2^{P}\Big(\frac{4}{(u+1)\varepsilon}\Big)^{P}.
--   $$
--
--   The compensated per-action variables are frozen at their first success and their inverse moments are controlled by the scalar interface with drift at least $\varepsilon$. A contraction argument on $D_\varepsilon$ then passes from the per-point moments to a uniform statement. This is the "far" part of the reference block bound.
--
--   **Formalization Note** Rounds are 0-based.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Appendix G, proof of Lemma G.29, (G.629)–(G.660) (pp.183–186)

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
variable (H : Sharp 𝒜 ℬ θ astar)
include H

theorem G26G.Sharp.far_prob (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {C : ℝ} (hC : 0 ≤ C)
    (hcor : IsCorruptedG P 𝒜 θ C T R)
    {τ : ℕ → ℝ} (hτpos : ∀ n, 0 < τ n) (hτmono : ∀ n, τ n ≤ τ (n + 1))
    (hδ : ∀ n, τ (n + 1) - τ n ≤ 1) {m0 u : ℕ} (h2uT : 2 * u ≤ T) (hm0u : m0 ≤ u)
    (hhalf : 2 * ((m0 : ℝ) + 1) ≤ (u : ℝ) + 1)
    (hmP : ((4 * kk d : ℕ) : ℝ) + 1 ≤ 2 * ((m0 : ℝ) + 1))
    (hτB : ∀ n, m0 ≤ n → gB d * (gbeta d (n + 1) + 3) ≤ τ n)
    (hτm : 2 * (((4 * kk d : ℕ) : ℝ) + 1) ≤ τ m0)
    (hτβ : ∀ n, m0 ≤ n → n < 2 * u →
      40 * (((4 * kk d : ℕ) : ℝ) + 1) * gbeta d (n + 1) * ((n : ℝ) + 1) ≤ τ m0 ^ 2)
    {ε : ℝ} (hε : 0 < ε) {hbv : ℝ} (hbC : hbv + 4 * C ≤ 2 * τ (2 * u))
    {ρ : ℝ} (hρa : 4 * τ (2 * u) ≤ ρ) (hρb : 2 * (4 * C + 2 * τ (2 * u)) ≤ ρ) :
    P.real {ω | ∃ s, u ≤ s ∧ s ≤ 2 * u ∧ ∃ a ∈ Dfar ℬ θ astar ε,
        (a - astar) ⬝ᵥ R.cumEst s ω ≤ hbv} ≤
      P.real (IW 𝒜 ℬ R θ astar C τ m0 (2 * u))ᶜ +
        2 ^ (4 * kk d) * cK d * (((2 * u : ℕ) : ℝ) + 1) ^ (4 * kk d) / ρ ^ (4 * kk d) +
        (2 * (4 * τ (2 * u))) ^ (4 * kk d) * (ρ / (4 * τ (2 * u))) ^ d *
          (2 ^ (4 * kk d) * (4 / (((u : ℝ) + 1) * ε)) ^ (4 * kk d)) := by sorry
