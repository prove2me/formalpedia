-- Prove2me | Theorems.Thm_IAFTRL_lemma_C_37_pos_moments
-- name    : IAFTRL.lemma_C_37_pos_moments
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-15T15:47:33.778222+00:00
-- url     : https://prove2.me/theorems/59baceab-70b6-43a1-83df-358eee05fbf8
-- title:
--   Lemma C.14 (v1) — positive local moments of the compensated process on a surviving window
-- statement:
--   Throughout, the processes satisfy the full-history scalar difference interface of Lemma C.34 (bundled as `C37.Iface`). There are $K$ actions with a distinguished action $a^*$ and gaps $\Delta(a^*)=0$, $\Delta_0\le\Delta(a)\le 2$. The processes satisfy $X_{0,a}=0$, $X_{t+1,a}=X_{t,a}+D_{t,a}$ and $D_{t,a^*}=0$, and $\mathbb E[D_{t,a}\mid\mathcal F_t]=\Delta(a)+e_{t,a}$ with $|e_{t,a}|\le2\kappa_t$, $\kappa_t\in[0,2]$ and $\sum_{t<T}\kappa_t\le C$. The increments obey $|D_{t,a}|\le 2\beta_{t+1}+(Z_{t,a}+Z_{t,a^*})/B$ and $\mathbb E[D_{t,a}^2\mid\mathcal F_t]\le 4\beta_{t+1}+2(Z_{t,a}^2+Z_{t,a^*}^2)/(B(t+1))$, where $Z_{t,a}=X_{t,a}-\min_bX_{t,b}$. Here $P=2\lceil256+\log(2K)\rceil$, $B=2^{24}P$, $k=K^{1/P}$, $\nu=3P/4$, and $n=t+1$ is the paper's round.
--
--   With the window $[m,t]$, threshold $\theta>0$, surviving-window indicator $I_s$ and compensated process $Y_s=X_{s,a}-\sum_{i<s}e_{i,a}+2C+2\theta$ as in Lemma C.30, assume:
--   - $3B\beta_{s+1}\le\theta$ and $\Delta(a)+5(P-1)\beta_{s+1}/\theta\le A$ for $m\le s<t$;
--   - the initial moment satisfies $\mathbb E[I_mY_m^P]\le w_0^P$ with $w_0>0$.
--
--   Then
--   $$
--   \mathbb E\bigl[I_t\,Y_t^{P}\bigr]\le\Bigl(\frac{A\,n}{1-\kappa_0}+w_0\Bigl(\frac{n}{m+1}\Bigr)^{2\kappa_0}\Bigr)^P,\qquad \kappa_0=\frac{2(P-1)}B .
--   $$
--   This is the positive local moment bound behind the distortion factor $\Psi_t$ of Lemma C.14. The linear term carries the drift $\Delta(a)$, and the initial moment decays relative to $n$ because $2\kappa_0<1$.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299v1, Lemma C.14 (C.118)–(C.125), pp.66–68, with Lemma C.29

import Mathlib
import Definitions.Def_IAFTRL_beta
import Definitions.Def_IAFTRL_Bc
import Definitions.Def_IAFTRL_C37_scalar

namespace IAFTRL

open MeasureTheory

/-- **Positive local moments.** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*,
arXiv:2611.01299v1, Lemma C.14 ((C.120)–(C.123)), for the abstract interface `C37.Iface`: on the
surviving window, if `3Bβ_{s+1} ≤ θ` and `Δ(a) + 5(P−1)β_{s+1}/θ ≤ A` for `m ≤ s < t`, and the
initial moment satisfies `E[I_m Y_m^P] ≤ w₀^P`, then
`E[I_t Y_t^P] ≤ (A n/(1 − κ₀) + w₀ (n/(m+1))^{2κ₀})^P` with `n = t + 1`, `κ₀ = 2(P−1)/B`. -/
theorem lemma_C_37_pos_moments {d K : ℕ} {jstar : Fin K} {Δ : Fin K → ℝ} {Δ₀ : ℝ} {Ω : Type*}
    [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {F : ℕ → MeasurableSpace Ω}
    {T : ℕ} {C : ℝ} {X D e : ℕ → Fin K → Ω → ℝ} {κ : ℕ → Ω → ℝ}
    (I : C37.Iface d K jstar Δ Δ₀ μ F T C X D e κ) (m : ℕ) (θ : ℝ) (t : ℕ) (a : Fin K)
    (hθ : 0 < θ) (hmt : m ≤ t) (htT : t ≤ T)
    (hQ1 : ∀ s, m ≤ s → s < t → 3 * Bc K * beta d K (s + 1) ≤ θ)
    (A : ℝ) (hA0 : 0 ≤ A)
    (hA : ∀ s, m ≤ s → s < t → Δ a + 5 * ((C37.Pord K : ℝ) - 1) * beta d K (s + 1) / θ ≤ A)
    (w0 : ℝ) (hw0 : 0 < w0)
    (hW0 : ∫ ω, C37.Ii C κ X m θ m ω * C37.Yc C θ X e m a ω ^ C37.Pord K ∂μ ≤ w0 ^ C37.Pord K) :
    ∫ ω, C37.Ii C κ X m θ t ω * C37.Yc C θ X e t a ω ^ C37.Pord K ∂μ ≤
      (A * ((t : ℝ) + 1) / (1 - C37.kap0 K) + w0 * (((t : ℝ) + 1) / ((m : ℝ) + 1)) ^ (2 * C37.kap0 K)) ^
        C37.Pord K := by sorry

end IAFTRL
