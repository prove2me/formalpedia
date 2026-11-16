-- Prove2me | Theorems.Thm_IAFTRL_lemma_C_37_inv_moments
-- name    : IAFTRL.lemma_C_37_inv_moments
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-15T15:47:34.012085+00:00
-- url     : https://prove2.me/theorems/0f4f2dcd-ffd1-4ea7-b36f-1396a7c9072c
-- title:
--   Lemmas C.29–C.30 (v1) — inverse local moments of the compensated process on a surviving window
-- statement:
--   Throughout, the processes satisfy the full-history scalar difference interface of Lemma C.34 (bundled as `C37.Iface`). There are $K$ actions with a distinguished action $a^*$ and gaps $\Delta(a^*)=0$, $\Delta_0\le\Delta(a)\le 2$. The processes satisfy $X_{0,a}=0$, $X_{t+1,a}=X_{t,a}+D_{t,a}$ and $D_{t,a^*}=0$, and $\mathbb E[D_{t,a}\mid\mathcal F_t]=\Delta(a)+e_{t,a}$ with $|e_{t,a}|\le2\kappa_t$, $\kappa_t\in[0,2]$ and $\sum_{t<T}\kappa_t\le C$. The increments obey $|D_{t,a}|\le 2\beta_{t+1}+(Z_{t,a}+Z_{t,a^*})/B$ and $\mathbb E[D_{t,a}^2\mid\mathcal F_t]\le 4\beta_{t+1}+2(Z_{t,a}^2+Z_{t,a^*}^2)/(B(t+1))$, where $Z_{t,a}=X_{t,a}-\min_bX_{t,b}$. Here $P=2\lceil256+\log(2K)\rceil$, $B=2^{24}P$, $k=K^{1/P}$, $\nu=3P/4$, and $n=t+1$ is the paper's round.
--
--   Fix a window $[m,t]$ and a threshold $\theta>0$. Let $I_s$ be the indicator that the budget is not exceeded before $s$ and that $F_j\le\theta^P$ for $m\le j\le s$. Consider the compensated process
--   $$
--   Y_s=X_{s,a}-\sum_{i<s}e_{i,a}+2C+2\theta .
--   $$
--   Assume $2(m+1)\le n$, $\theta\ge2(P+1)$, $P+1\le2(m+1)$, and the local thresholds $3B\beta_{s+1}\le\theta$ and $20(P+1)\beta_{s+1}(s+1)\le\theta^2$ for $m\le s<t$. Then for every $a\ne a^*$,
--   $$
--   \mathbb E\bigl[I_t\,Y_t^{-P}\bigr]\le\Bigl(\frac{4}{n\,\Delta(a)}\Bigr)^P .
--   $$
--   On the surviving window, $Y_s\ge\theta$ and the increments satisfy (C.198). The inverse moment controls small estimated gaps and hence the failure probability of the common good event (Lemma C.26).
--
--   **Formalization Note** $Y_t^{-P}$ is written $(1/\max(\theta,Y_t))^P$; the two agree on $\{I_t=1\}$.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299v1, Lemma C.29 (C.197)–(C.200) and Lemma C.30 (C.201)–(C.205), pp.81–83

import Mathlib
import Definitions.Def_IAFTRL_beta
import Definitions.Def_IAFTRL_Bc
import Definitions.Def_IAFTRL_C37_scalar

namespace IAFTRL

open MeasureTheory

/-- **Inverse local moments.** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*,
arXiv:2611.01299v1, Lemmas C.29–C.30 ((C.198), (C.201)), for the abstract interface `C37.Iface`:
on the surviving window `I_s` (budget not exceeded, `F_j ≤ θ^P` for `m ≤ j ≤ s`) the compensated
process `Y_t = X_{t,a} − Σ_{i<t} e_{i,a} + 2C + 2θ` satisfies `E[I_t Y_t^{−P}] ≤ (4/(nΔ(a)))^P`,
provided `2(m+1) ≤ n = t + 1`, `θ ≥ 2(P+1)`, `P + 1 ≤ 2(m+1)` and the local thresholds
`3Bβ_{s+1} ≤ θ`, `20(P+1)β_{s+1}(s+1) ≤ θ²` hold on the window. -/
theorem lemma_C_37_inv_moments {d K : ℕ} {jstar : Fin K} {Δ : Fin K → ℝ} {Δ₀ : ℝ} {Ω : Type*}
    [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {F : ℕ → MeasurableSpace Ω}
    {T : ℕ} {C : ℝ} {X D e : ℕ → Fin K → Ω → ℝ} {κ : ℕ → Ω → ℝ}
    (I : C37.Iface d K jstar Δ Δ₀ μ F T C X D e κ) (m : ℕ) (θ : ℝ) (t : ℕ) (a : Fin K)
    (hθ : 0 < θ) (ha : a ≠ jstar) (hmt : m ≤ t) (htT : t ≤ T)
    (hmhalf : 2 * ((m : ℝ) + 1) ≤ (t : ℝ) + 1)
    (hθP : 2 * ((C37.Pord K : ℝ) + 1) ≤ θ) (hmP : (C37.Pord K : ℝ) + 1 ≤ 2 * ((m : ℝ) + 1))
    (hQ1 : ∀ s, m ≤ s → s < t → 3 * Bc K * beta d K (s + 1) ≤ θ)
    (hQ2 : ∀ s, m ≤ s → s < t →
      20 * ((C37.Pord K : ℝ) + 1) * beta d K (s + 1) * ((s : ℝ) + 1) ≤ θ ^ 2) :
    ∫ ω, C37.Ii C κ X m θ t ω * (1 / max θ (C37.Yc C θ X e t a ω)) ^ C37.Pord K ∂μ ≤
      (4 / (((t : ℝ) + 1) * Δ a)) ^ C37.Pord K := by sorry

end IAFTRL
