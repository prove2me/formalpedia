-- Prove2me | Theorems.Thm_NondomArb_OptDecomp_lemma_4_6
-- name    : NondomArb.OptDecomp.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:16:09.962096+00:00
-- url     : https://prove2.me/theorems/8c4e1951-8878-4bc7-9e85-a62b5a6d0cf9
-- title:
--   Lemma 4.6 — N_t, where one-period no-arbitrage fails, is universally measurable, and 𝒫-polar under NA(𝒫)
-- statement:
--   Consider the nondominated market of §1.2 without options ($e = 0$): $\Omega_t = \Omega_1^t$ with $\Omega_1$ Polish, one-period model sets $\mathcal P_t(\omega)$ (nonempty, convex, with analytic graph), Borel stock prices $S_t$, and the set $\mathcal P$ of possible models. For $\omega \in \Omega_t$, NA($\mathcal P_t(\omega)$) is the no-arbitrage condition of the one-period market with increment $\Delta S_{t+1}(\omega, \cdot) = S_{t+1}(\omega, \cdot) - S_t(\omega)$ under $\mathcal P_t(\omega)$.
--
--   **Lemma 4.6.** Let $t \in \{0, \dots, T-1\}$. The set
--   $$N_t = \{\omega \in \Omega_t : \mathrm{NA}(\mathcal P_t(\omega)) \text{ fails}\}$$
--   is universally measurable, and if NA($\mathcal P$) holds, then $N_t$ is $\mathcal P$-polar.
--
--   The lemma localizes the multi-period no-arbitrage condition: under NA($\mathcal P$), the one-period markets are arbitrage-free outside a polar set of nodes. It is the step that lets the proof of the optional decomposition discard the nodes where the one-period duality is unavailable.
--
--   **Formalization Note.** $N_t \subseteq \Omega_t$ is seen in $\Omega$ through the prefix map $\omega \mapsto (\omega_1, \dots, \omega_t)$, so "$\mathcal P$-polar" means $P(\{\omega : (\omega_1, \dots, \omega_t) \in N_t\}) = 0$ for every $P \in \mathcal P$.
-- source:
--   Bouchard, Nutz, Arbitrage and duality in nondominated discrete-time models, arXiv:1305.6008v3, p. 21, Lemma 4.6

import Mathlib
import Definitions.Def_BertsekasShreve_AnalyticSelection_Measurability
import Definitions.Def_NondomArb_OptDecomp_Model

open MeasureTheory BertsekasShreve.AnalyticSelection

namespace NondomArb.OptDecomp

/-- **Lemma 4.6** (Bouchard–Nutz, p. 21). In the market of §1.2 without options (`e = 0`), let
`t ∈ {0, …, T − 1}`. The set `N_t = {ω ∈ Ω_t : NA(𝒫_t(ω)) fails}` is universally measurable,
and if `NA(𝒫)` holds, then `N_t` (seen in `Ω` through the prefix map) is `𝒫`-polar. -/
theorem lemma_4_6 {Ω₁ : Type*} [TopologicalSpace Ω₁] [PolishSpace Ω₁] [MeasurableSpace Ω₁]
    [BorelSpace Ω₁] {T d : ℕ} (M : Market Ω₁ T d 0) (hM : M.Standing)
    (t : ℕ) (ht : t < T) :
    IsUniversallyMeasurable (M.badSet t) ∧
      (M.NA → M.IsPolar ((fun ω => NondomArb.Superhedge.pre ω t ht.le) ⁻¹' M.badSet t)) := by sorry

end NondomArb.OptDecomp
