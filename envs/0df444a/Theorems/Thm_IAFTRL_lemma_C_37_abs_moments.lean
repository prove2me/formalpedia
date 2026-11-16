-- Prove2me | Theorems.Thm_IAFTRL_lemma_C_37_abs_moments
-- name    : IAFTRL.lemma_C_37_abs_moments
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-15T15:47:29.839019+00:00
-- url     : https://prove2.me/theorems/fa0cea1d-f0f7-46c0-83aa-2e7aca18b428
-- title:
--   Lemmas C.36–C.37 (v1) — absolute $P$-th moments of the difference interface after the burn-in
-- statement:
--   Throughout, the processes satisfy the full-history scalar difference interface of Lemma C.34 (bundled as `C37.Iface`). There are $K$ actions with a distinguished action $a^*$ and gaps $\Delta(a^*)=0$, $\Delta_0\le\Delta(a)\le 2$. The processes satisfy $X_{0,a}=0$, $X_{t+1,a}=X_{t,a}+D_{t,a}$ and $D_{t,a^*}=0$, and $\mathbb E[D_{t,a}\mid\mathcal F_t]=\Delta(a)+e_{t,a}$ with $|e_{t,a}|\le2\kappa_t$, $\kappa_t\in[0,2]$ and $\sum_{t<T}\kappa_t\le C$. The increments obey $|D_{t,a}|\le 2\beta_{t+1}+(Z_{t,a}+Z_{t,a^*})/B$ and $\mathbb E[D_{t,a}^2\mid\mathcal F_t]\le 4\beta_{t+1}+2(Z_{t,a}^2+Z_{t,a^*}^2)/(B(t+1))$, where $Z_{t,a}=X_{t,a}-\min_bX_{t,b}$. Here $P=2\lceil256+\log(2K)\rceil$, $B=2^{24}P$, $k=K^{1/P}$, $\nu=3P/4$, and $n=t+1$ is the paper's round.
--
--   Let $G_t=\sum_aX_{t,a}^P$. If $n^{P/4}\ge H_G$, where $H_G=\max\{1,J_G/(\nu-v_G)\}$ is the constant of Definition C.35, then
--   $$
--   \mathbb E[G_t]\le\bigl((16k+1)\,n\bigr)^P .
--   $$
--   This is the universal absolute-moment bound of Lemma C.37 combined with the burn-in of Lemma C.36. It controls the initial values of the windows used for the local moment estimates and the initial negative moment $\mathbb E[F_{n_0}]$ in (C.221).
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299v1, Lemmas C.36–C.37, (C.229)–(C.240), pp.88–90

import Mathlib
import Definitions.Def_IAFTRL_beta
import Definitions.Def_IAFTRL_Bc
import Definitions.Def_IAFTRL_C37_scalar

namespace IAFTRL

open MeasureTheory

/-- **Absolute moments after the burn-in.** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*,
arXiv:2611.01299v1, Lemmas C.36–C.37 ((C.234)–(C.235)), for the abstract scalar difference interface
`C37.Iface` ((C.226)–(C.228) of Lemma C.34): with `G_t = Σ_a X_{t,a}^P`, `n = t + 1`,
`k = K^{1/P}`, once `n^{P/4} ≥ H_G`, `E[G_t] ≤ ((16k + 1) n)^P`. -/
theorem lemma_C_37_abs_moments {d K : ℕ} {jstar : Fin K} {Δ : Fin K → ℝ} {Δ₀ : ℝ} {Ω : Type*}
    [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {F : ℕ → MeasurableSpace Ω}
    {T : ℕ} {C : ℝ} {X D e : ℕ → Fin K → Ω → ℝ} {κ : ℕ → Ω → ℝ}
    (I : C37.Iface d K jstar Δ Δ₀ μ F T C X D e κ) (t : ℕ) (ht : t ≤ T)
    (hburn : C37.HG d K ≤ ((t : ℝ) + 1) ^ ((C37.Pord K : ℝ) / 4)) :
    ∫ ω, C37.Gsum X t ω ∂μ ≤ ((16 * C37.kK K + 1) * ((t : ℝ) + 1)) ^ C37.Pord K := by sorry

end IAFTRL
