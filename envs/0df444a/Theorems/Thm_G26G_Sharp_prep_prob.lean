-- Prove2me | Theorems.Thm_G26G_Sharp_prep_prob
-- name    : G26G.Sharp.prep_prob
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-18T00:30:58.5494+00:00
-- url     : https://prove2.me/theorems/f8ffebe4-f37b-4077-a719-8c06384e9e7c
-- title:
--   Preparation before a reference block: probability that the remaining-budget field crosses its buffer
-- statement:
--   **Setting.** $\mathcal A\subseteq\mathbb R^d$ is a compact action set spanning $\mathbb R^d$, $\mathcal B\subseteq\mathcal A$ is a compact generator ($\mathcal A\subseteq\mathcal K:=\operatorname{Conv}\mathcal B$), $e:\mathbb N\to\mathbb Q^d$ is the direction enumeration, and $R$ is a GIA-FTRL run of $T$ rounds (`IsGIAFTRLRun`) with cumulative loss estimate $S_n=\sum_{j<n}\hat\theta_j$, run filtration $(\mathcal G_n)$, learning rate $\beta_n=16d+\sqrt n$ (`gbeta`) and magnitude constant $B=2^{36}(d+1)$ (`gB`). The filtration used below is $\mathcal F_n=\mathcal G_n$ for $n<T$ and $\mathcal F_T=\mathcal F$ (`Fx`). The standing hypotheses `Sharp` hold: $\mathcal A$ lies in the unit ball, $k=\dim\mathcal K\ge1$, $\|\theta\|_{\mathcal A}\le1$, $a^*\in\mathcal A$ is the unique minimizer of $a\mapsto a^\top\theta$ on $\mathcal A$, and the instance is sharp with modulus $\varsigma>0$ (`H.sig`): $\Delta(a)=(a-a^*)^\top\theta\ge\varsigma\|a-a^*\|_{\mathcal S}$ on $\mathcal K$. The corruption is bounded by $C$: $\sum_{t<T}\|\theta_t-\theta\|_{\mathcal A}\le C$ a.s. (`IsCorruptedG`). The projective body is $U_\theta=\overline{\{\Delta(a)^{-1}(a-a^*):a\in\mathcal K\setminus\{a^*\}\}}$ and the cone body is $D_\theta=\{\lambda u:\lambda\in[0,1],u\in U_\theta\}$; $\Lambda=\varsigma^{-1}$, $A_n=\sum_{j<n}\|\theta_j-\theta\|_{\mathcal A}$, and $j^*$ is the index of $a^*$ among the reference atoms (`js`).
--
--   Let $C\ge0$, let $\tau$ be nondecreasing, $m_0\le n_C\le N\le T$, $\tau_{m_0}\ge1$, and $\rho\ge\max\{\tau_{m_0},4C\}$. Write $P=4k$ with $k=1024(d+1)$ (`kk d`), $c_K$ (`cK d`) for the absolute-envelope constant, and $I^W_N$ for the event that the remaining-budget field $W$ of Lemma G.30 satisfies $\max_{\mathcal K}(-W_j)\le\tau_j$ for all $m_0\le j\le N$. Then
--   $$
--   \mathbb P\big((I^W_N)^c\big)\le\frac{2^{P}c_K(N+1)^{P}}{\rho^{P}}+\frac{2^{P}4^{d}(\rho/\tau_{m_0})^{d}}{\tau_{m_0}^{P}}\Big(H_{\rm neg}(k,16d+1,B)(N+1)^{3k}+\Big(\frac{N+1}{n_C+1}\Big)^{d+2}2^{P}\big(c_K(n_C+1)^{P}+(2C)^{P}\big)\Big).
--   $$
--
--   The first term is Markov's inequality for the absolute envelope of $W$; the second applies the crossing envelope from the start $n_C$, where the negative moment of $W$ is bounded by its absolute moment plus the shift $2C$. This is the event $\{I=0\}$ that the block argument of Lemma G.29 must exclude before using the per-action variables.
--
--   **Formalization Note** Rounds are 0-based.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Appendix G, proof of Lemma G.29, (G.623)–(G.628) (pp.182–183), with Lemma G.30 (G.678) (p.188)

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
variable (he : Function.Surjective e)
include he

theorem G26G.Sharp.prep_prob (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {C : ℝ} (hC : 0 ≤ C)
    (hcor : IsCorruptedG P 𝒜 θ C T R) {τ : ℕ → ℝ} (hτmono : ∀ n, τ n ≤ τ (n + 1))
    {m0 N nC : ℕ} (hN : N ≤ T) (hnN : nC ≤ N) (hτ1 : 1 ≤ τ m0) {ρ : ℝ} (hρτ : τ m0 ≤ ρ)
    (hρC : 4 * C ≤ ρ) :
    P.real (IW 𝒜 ℬ R θ astar C τ m0 N)ᶜ ≤
      2 ^ (4 * kk d) * cK d * ((N : ℝ) + 1) ^ (4 * kk d) / ρ ^ (4 * kk d) +
      2 ^ (4 * kk d) * 4 ^ d * (ρ / τ m0) ^ d / τ m0 ^ (4 * kk d) *
        (Hneg (kk d) (16 * d + 1) (gB d) * ((N : ℝ) + 1) ^ (3 * kk d) +
          (((N : ℝ) + 1) / ((nC : ℝ) + 1)) ^ (d + 2) *
            (2 ^ (4 * kk d) * (cK d * ((nC : ℝ) + 1) ^ (4 * kk d) + (2 * C) ^ (4 * kk d)))) := by sorry
