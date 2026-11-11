-- Prove2me | Theorems.Thm_MultiOmniRate_Lipschitz_lemma_3_4
-- name    : MultiOmniRate.Lipschitz.lemma_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:23:28.734427+00:00
-- url     : https://prove2.me/theorems/b59b710a-46c5-47d1-9dc8-e713351d00ae
-- title:
--   Lemma 3.4 — Decision OI of the smoothed prediction $\le\sup_\ell|\mathbb E\langle w_{\ell,r}(q(x)),e_y-q(x)\rangle|+2r$
-- statement:
--   Let $K\ge2$, $0<r\le1/2$, $\mathcal D$ a distribution on $\mathcal X\times\mathcal Y$, $q$ a base predictor and $p$ the randomized prediction of (3.1), $p(x)=(1-r)q(x)+rz$ with $z\sim\mathrm{Unif}(\Delta_K)$ fresh. For every class $\mathcal L$ of bounded losses (measurable, with measurable best responses),
--   $$\mathrm{DecOI}_{\mathcal L}(p)\ \le\ \sup_{\ell\in\mathcal L}\Big|\mathbb E\big[\langle w_{\ell,r}(q(x)),\,e_y-q(x)\rangle\big]\Big|+2r .$$
--
--   Smoothing therefore replaces the discontinuous decision weights by the continuous $w_{\ell,r}$, evaluated at the base prediction, at an additive cost $2r$.
--
--   Differences from the source:
--   - encoding: labels $\mathcal Y=\{0,\dots,K-1\}$ → `Fin K`, with `[NeZero K]` (implied by $K\ge2$) so that label $0$ exists; reason: relabeling; same instances
--   - encoding: randomized predictor $\mathcal X\to\Delta(\Delta_K)$; modeled label $\tilde y\sim p(x)$ → Markov kernel `Kernel X (Simplex K)`; $\mathbb E_{\tilde y\sim a}\ell(\cdot,\tilde y)$ written as $\langle a,\ell(\cdot,\cdot)\rangle$; reason: footnote 3 (p. 19); the modeled-label expectation is exact
--   - reading: "we fix a measurable best response" (p. 19); benchmark rules $h$ → each $\ell\in\mathcal L$ is measurable in the action with measurable $\mathrm{BR}_\ell$ (`BRLoss.IsMeasurable`), each $h\in\mathcal H$ is measurable; reason: the paper's standing convention; it is what makes every expectation defined
--   - generalization: base prediction $q(x)$ of (3.1) → $q$ is any randomized base predictor (Markov kernel); expectations also average over its randomness; reason: a deterministic $q$ is the Dirac kernel; Algorithm 1 uses the randomized base prediction $q_\tau(x)$
--   - encoding: $\mathrm{Unif}(\Delta_K)$ → `unifSimplex K`: normalized Lebesgue measure on the free coordinates $(p_1,\dots,p_{K-1})$, pushed to $\Delta_K$; reason: the uniform distribution on the simplex, as in the proof of Lemma 3.3 (App. A.1)
--   - encoding: suprema over a loss class (empty class: $-\infty$) → real `⨆` over the class; every term is bounded by $2$ in absolute value, and the empty supremum is $0$; reason: an empty $\mathcal L$ makes every side $0$, which the inequality covers as the paper's convention does
-- source:
--   Rivkin, Okoroafor, Kim, The Sample Complexity of Multi-Class Omniprediction, STOC 2027 submission (manuscript sha256 135d9904…), p. 26, Lemma 3.4 (proof: p. 54, App. A.1)

import Mathlib
import Definitions.Def_MultiOmniRate_Lipschitz_Setting
import Definitions.Def_MultiOmniRate_Lipschitz_OmniErrors
import Definitions.Def_MultiOmniRate_Lipschitz_Smoothing

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace MultiOmniRate.Lipschitz

theorem lemma_3_4 {K : ℕ} [NeZero K] (hK : 2 ≤ K) {X A : Type*} [MeasurableSpace X]
    [MeasurableSpace A] (L : Set (BRLoss K A)) (hL : ∀ ℓ ∈ L, ℓ.IsMeasurable)
    (D : Measure (X × Fin K)) [IsProbabilityMeasure D]
    (q : Kernel X (Simplex K)) [IsMarkovKernel q] (r : ℝ) (hr0 : 0 < r) (hr1 : r ≤ 1 / 2) :
    DecOI L D (smoothKernel r q) ≤
      (⨆ ℓ : L, |∫ ω, dot (smoothW r (ℓ : BRLoss K A).pr ω.2) (resid ω.1.2 ω.2) ∂(jointLaw D q)|)
        + 2 * r := by sorry

end MultiOmniRate.Lipschitz
