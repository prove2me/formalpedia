-- Prove2me | Theorems.Thm_G26G_Sharp_ref_block
-- name    : G26G.Sharp.ref_block
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-18T00:30:43.578695+00:00
-- url     : https://prove2.me/theorems/38dcb71b-29c0-4464-b299-468d50b46699
-- title:
--   Lemma G.29 (corruption-uniform block bound for the reference)
-- statement:
--   **Setting.** $\mathcal A\subseteq\mathbb R^d$ is a compact action set spanning $\mathbb R^d$, $\mathcal B\subseteq\mathcal A$ is a compact generator ($\mathcal A\subseteq\mathcal K:=\operatorname{Conv}\mathcal B$), $e:\mathbb N\to\mathbb Q^d$ is the direction enumeration, and $R$ is a GIA-FTRL run of $T$ rounds (`IsGIAFTRLRun`) with cumulative loss estimate $S_n=\sum_{j<n}\hat\theta_j$, run filtration $(\mathcal G_n)$, learning rate $\beta_n=16d+\sqrt n$ (`gbeta`) and magnitude constant $B=2^{36}(d+1)$ (`gB`). The filtration used below is $\mathcal F_n=\mathcal G_n$ for $n<T$ and $\mathcal F_T=\mathcal F$ (`Fx`). The standing hypotheses `Sharp` hold: $\mathcal A$ lies in the unit ball, $k=\dim\mathcal K\ge1$, $\|\theta\|_{\mathcal A}\le1$, $a^*\in\mathcal A$ is the unique minimizer of $a\mapsto a^\top\theta$ on $\mathcal A$, and the instance is sharp with modulus $\varsigma>0$ (`H.sig`): $\Delta(a)=(a-a^*)^\top\theta\ge\varsigma\|a-a^*\|_{\mathcal S}$ on $\mathcal K$. The corruption is bounded by $C$: $\sum_{t<T}\|\theta_t-\theta\|_{\mathcal A}\le C$ a.s. (`IsCorruptedG`). The projective body is $U_\theta=\overline{\{\Delta(a)^{-1}(a-a^*):a\in\mathcal K\setminus\{a^*\}\}}$ and the cone body is $D_\theta=\{\lambda u:\lambda\in[0,1],u\in U_\theta\}$; $\Lambda=\varsigma^{-1}$, $A_n=\sum_{j<n}\|\theta_j-\theta\|_{\mathcal A}$, and $j^*$ is the index of $a^*$ among the reference atoms (`js`).
--
--   Assume $e$ is surjective. Let $C\ge0$, $n_C\ge1$ an integer with $C\le n_C$, and let $u$ be an integer with $2u\le T$, $u\ge S_{\rm ref}$ (`H.Sref he`) and
--   $$
--   u+1\ge2^{20}(n_C+1)\log\big(e(n_C+1)\big).
--   $$
--   Then the probability that the penalized reference problem (3.4) fails to select $a^*$ strictly at some round of the block $[u,2u]$ satisfies
--   $$
--   \mathbb P\big(\exists s\in[u,2u]:\ \neg\,\mathrm{good}(s+1,S_s)\big)\le D_{\rm ref}\Big(\Big(\frac{n_C+1}{u+1}\Big)^4+\frac1{(u+1)^4}\Big),
--   $$
--   where $\mathrm{good}(n,S)$ (`goodS`) says the atom of $a^*$ is the strict minimizer in (3.4), and $D_{\rm ref}$ (`H.Dref he`) depends only on the instance.
--
--   This is (G.622) of Lemma G.29 with $a=4$ and $n_C$ in the role of the corruption scale. Summed over dyadic blocks it gives the reference part of the alive-window failure probability in Lemma G.28.
--
--   **Formalization Note** Rounds are 0-based (block $[u,2u]$ in run indices).
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Appendix G, Lemma G.29, (G.621)–(G.622) (p.182)

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

theorem G26G.Sharp.ref_block (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {C : ℝ} (hC : 0 ≤ C)
    (hcor : IsCorruptedG P 𝒜 θ C T R) {u nC : ℕ} (hnC1 : 1 ≤ nC) (hCn : C ≤ nC)
    (h2uT : 2 * u ≤ T) (hu : H.Sref he ≤ u)
    (huC : 2 ^ 20 * (((nC : ℝ) + 1) * Real.log (Real.exp 1 * ((nC : ℝ) + 1))) ≤ (u : ℝ) + 1) :
    P.real {ω | ∃ s, u ≤ s ∧ s ≤ 2 * u ∧ ¬ goodS ℬ e (js ℬ e astar) (s + 1) (R.cumEst s ω)} ≤
      H.Dref he * ((((nC : ℝ) + 1) / ((u : ℝ) + 1)) ^ 4 + 1 / ((u : ℝ) + 1) ^ 4) := by sorry
