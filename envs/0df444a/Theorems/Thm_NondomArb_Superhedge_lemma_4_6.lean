-- Prove2me | Theorems.Thm_NondomArb_Superhedge_lemma_4_6
-- name    : NondomArb.Superhedge.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:23:16.052843+00:00
-- url     : https://prove2.me/theorems/a3a22d61-9197-4f67-8569-850efe798703
-- title:
--   Lemma 4.6 — N_t = {NA(𝒫_t(ω)) fails} is universally measurable, and 𝒫-polar under NA(𝒫)
-- statement:
--   Consider the multi-period market of §1.2 without options ($e=0$). For $t<T$ and $\omega\in\Omega_t$, $\mathrm{NA}(\mathcal P_t(\omega))$ is the one-period no-arbitrage condition for the increment $\Delta S_{t+1}(\omega,\cdot)=S_{t+1}(\omega,\cdot)-S_t(\omega)$ under $\mathcal P_t(\omega)$.
--
--   **Lemma.** Let $t\in\{0,\dots,T-1\}$. The set
--   $$N_t=\{\omega\in\Omega_t:\ \mathrm{NA}(\mathcal P_t(\omega))\text{ fails}\}$$
--   is universally measurable, and if NA($\mathcal P$) holds, then $N_t$ is $\mathcal P$-polar.
--
--   Global absence of arbitrage thus forces absence of arbitrage in quasi every one-period sub-market.
--
--   **Formalization Note** $N_t\subseteq\Omega_t$ is viewed in $\Omega$ through the first $t$ coordinates: its preimage under $\omega\mapsto(\omega_1,\dots,\omega_t)$ is $P$-null for every $P\in\mathcal P$.
-- source:
--   Bouchard, Nutz, Arbitrage and duality in nondominated discrete-time models, arXiv:1305.6008v3, p. 21, Lemma 4.6

import Mathlib
import Definitions.Def_BertsekasShreve_AnalyticSelection_Measurability
import Definitions.Def_NondomArb_Superhedge_Basic
import Definitions.Def_NondomArb_Superhedge_Model
open MeasureTheory BertsekasShreve.AnalyticSelection

namespace NondomArb.Superhedge

/-- **Lemma 4.6** (p. 21). (No options, `e = 0`.) The set `N_t` of `ω ∈ Ω_t` where the one-period
condition NA(𝒫_t(ω)) fails is universally measurable, and under NA(𝒫) it is `𝒫`-polar (as a
subset of `Ω` through the first `t` coordinates). -/
theorem lemma_4_6 {Ω₁ : Type*} [TopologicalSpace Ω₁] [PolishSpace Ω₁]
    [MeasurableSpace Ω₁] [BorelSpace Ω₁] {T d : ℕ}
    (M : Market Ω₁ T d 0) (hM : M.Standing) (t : ℕ) (ht : t < T) :
    IsUniversallyMeasurable (M.badSet t) ∧
      (M.NA → M.IsPolar ((fun ω => pre ω t ht.le) ⁻¹' M.badSet t)) := by sorry

end NondomArb.Superhedge
