-- Prove2me | Theorems.Thm_IAFTRL_lemma_C_37_window
-- name    : IAFTRL.lemma_C_37_window
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-15T15:47:29.793374+00:00
-- url     : https://prove2.me/theorems/4e24f043-2ace-43ad-a927-b9ac797aecca
-- title:
--   Lemmas C.31, C.33, C.28 (v1) — stopped negative moments and the window failure probability
-- statement:
--   Throughout, the processes satisfy the full-history scalar difference interface of Lemma C.34 (bundled as `C37.Iface`). There are $K$ actions with a distinguished action $a^*$ and gaps $\Delta(a^*)=0$, $\Delta_0\le\Delta(a)\le 2$. The processes satisfy $X_{0,a}=0$, $X_{t+1,a}=X_{t,a}+D_{t,a}$ and $D_{t,a^*}=0$, and $\mathbb E[D_{t,a}\mid\mathcal F_t]=\Delta(a)+e_{t,a}$ with $|e_{t,a}|\le2\kappa_t$, $\kappa_t\in[0,2]$ and $\sum_{t<T}\kappa_t\le C$. The increments obey $|D_{t,a}|\le 2\beta_{t+1}+(Z_{t,a}+Z_{t,a^*})/B$ and $\mathbb E[D_{t,a}^2\mid\mathcal F_t]\le 4\beta_{t+1}+2(Z_{t,a}^2+Z_{t,a^*}^2)/(B(t+1))$, where $Z_{t,a}=X_{t,a}-\min_bX_{t,b}$. Here $P=2\lceil256+\log(2K)\rceil$, $B=2^{24}P$, $k=K^{1/P}$, $\nu=3P/4$, and $n=t+1$ is the paper's round.
--
--   Let $b_j=C-\sum_{s<j}\kappa_s$ be the remaining budget and $F_j=\sum_a(2b_j-X_{j,a})_+^P$ the power sum of negative parts of the budget-shifted differences. Fix a start time $t_0$ with $n_0=t_0+1$, $n_0^{P/4}\ge H_G$ and $C\le n_0$, a window $[m,t]$ with $t_0\le m\le t<T$, and a level $L\ge0$. Then
--   $$
--   L\cdot\mathbb P\bigl(\exists\,j\in[m,t]:\ F_j>L\bigr)\le H_0\,n^\nu+(64\,n_0)^P\Bigl(\frac n{n_0}\Bigr)^{q},
--   $$
--   where $H_0$ and $q=\lceil v\rceil$ are the negative-moment constants (Definition C.32, with $v=6P^2k^2/B+P/4096$).
--
--   The bound combines the shifted negative-moment recursion $\mathbb E[F_{t+1}\mid\mathcal F_t]\le(1+v/n)F_t+J_0n^{\nu-1}$, its initialization $\mathbb E[F_{n_0}]\le(64n_0)^P$, and the stopped process of Lemma C.28. It is the window-failure input of Lemma C.26.
--
--   **Formalization Note** The left side is $L\,\mathbb E[1-\sigma_{t+1}]$, where $\sigma_s$ is the indicator of $\{F_j\le L,\ m\le j<s\}$ (`C37.sv`).
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299v1, Lemma C.31 (C.206)–(C.209), Lemma C.33 (C.210)–(C.222), Lemma C.28 (C.193)–(C.194), pp.80–86

import Mathlib
import Definitions.Def_IAFTRL_beta
import Definitions.Def_IAFTRL_Bc
import Definitions.Def_IAFTRL_C37_scalar

namespace IAFTRL

open MeasureTheory

/-- **Window failure probability via stopped negative moments.** Zhao–Tan, *Best-of-Both-Worlds FTRL
for Linear Bandits*, arXiv:2611.01299v1, Lemmas C.31, C.33 and C.28 ((C.193)–(C.194)), for the abstract
interface `C37.Iface`: with `F_j = Σ_a (2b_j − X_{j,a})_+^P` (`b_j = C − Σ_{s<j} κ_s`), a start time
`t₀` after the burn-in with `C ≤ t₀ + 1`, a window `[m, t]` with `t₀ ≤ m`, and any level `L ≥ 0`,
`L · P(∃ j ∈ [m, t], F_j > L) ≤ H_0 n^ν + (64 n₀)^P (n/n₀)^q` where `n = t + 1`, `n₀ = t₀ + 1`. -/
theorem lemma_C_37_window {d K : ℕ} {jstar : Fin K} {Δ : Fin K → ℝ} {Δ₀ : ℝ} {Ω : Type*}
    [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {F : ℕ → MeasurableSpace Ω}
    {T : ℕ} {C : ℝ} {X D e : ℕ → Fin K → Ω → ℝ} {κ : ℕ → Ω → ℝ}
    (I : C37.Iface d K jstar Δ Δ₀ μ F T C X D e κ) (t0 m t : ℕ) (L : ℝ)
    (hL : 0 ≤ L) (ht0m : t0 ≤ m) (hmt : m ≤ t) (htT : t ≤ T)
    (hburn : C37.HG d K ≤ ((t0 : ℝ) + 1) ^ ((C37.Pord K : ℝ) / 4)) (hCn : C ≤ (t0 : ℝ) + 1) :
    L * ∫ ω, (1 - C37.sv C κ X m L (t + 1) ω) ∂μ ≤ C37.HN d K * ((t : ℝ) + 1) ^ C37.nuP K +
      (64 * ((t0 : ℝ) + 1)) ^ C37.Pord K * (((t : ℝ) + 1) / ((t0 : ℝ) + 1)) ^ C37.qN K := by sorry

end IAFTRL
