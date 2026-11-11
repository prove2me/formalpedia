-- Prove2me | Theorems.Thm_MultiOmniRate_Lipschitz_lemma_3_5
-- name    : MultiOmniRate.Lipschitz.lemma_3_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:23:35.355536+00:00
-- url     : https://prove2.me/theorems/db20ae14-3c68-4610-bba3-b8f58951bfeb
-- title:
--   Lemma 3.5 — Hypothesis OI is $1$-Lipschitz in the prediction ($\ell_1$); $+2r$ for (3.1)
-- statement:
--   Let $K\ge2$, $\mathcal D$ a distribution on $\mathcal X\times\mathcal Y$, $\mathcal L$ a class of bounded losses (measurable, with measurable best responses) and $\mathcal H$ a nonempty class of measurable benchmark rules.
--
--   1. For any two predictors coupled on the same context, with predictions $p(x),q(x)$,
--   $$\mathrm{HypOI}_{\mathcal L,\mathcal H}(p)\le\mathrm{HypOI}_{\mathcal L,\mathcal H}(q)+\mathbb E\big[\|p(x)-q(x)\|_1\big].$$
--   2. In particular, for $0<r\le1/2$ the prediction (3.1), $p(x)=(1-r)q(x)+rz$ with $z\sim\mathrm{Unif}(\Delta_K)$, satisfies $\mathrm{HypOI}_{\mathcal L,\mathcal H}(p)\le\mathrm{HypOI}_{\mathcal L,\mathcal H}(q)+2r$.
--
--   Together with Lemma 3.4 this reduces both OI errors of the reported prediction to correlations at the base prediction.
--
--   Differences from the source:
--   - encoding: labels $\mathcal Y=\{0,\dots,K-1\}$ → `Fin K`, with `[NeZero K]` (implied by $K\ge2$) so that label $0$ exists; reason: relabeling; same instances
--   - encoding: randomized predictor $\mathcal X\to\Delta(\Delta_K)$; modeled label $\tilde y\sim p(x)$ → Markov kernel `Kernel X (Simplex K)`; $\mathbb E_{\tilde y\sim a}\ell(\cdot,\tilde y)$ written as $\langle a,\ell(\cdot,\cdot)\rangle$; reason: footnote 3 (p. 19); the modeled-label expectation is exact
--   - reading: "we fix a measurable best response" (p. 19); benchmark rules $h$ → each $\ell\in\mathcal L$ is measurable in the action with measurable $\mathrm{BR}_\ell$ (`BRLoss.IsMeasurable`), each $h\in\mathcal H$ is measurable; reason: the paper's standing convention; it is what makes every expectation defined
--   - encoding: two predictors "coupled on the same context" → a Markov kernel $\kappa:\mathcal X\to\Delta_K\times\Delta_K$; $p,q$ are its marginal kernels and $\mathbb E\|p(x)-q(x)\|_1$ is taken under $(x,y)\sim\mathcal D$, $\kappa(x)$; reason: a coupling is a joint law given the context
--   - generalization: base prediction $q(x)$ of (3.1) → $q$ is any randomized base predictor (Markov kernel); expectations also average over its randomness; reason: a deterministic $q$ is the Dirac kernel; Algorithm 1 uses the randomized base prediction $q_\tau(x)$
--   - encoding: $\mathrm{Unif}(\Delta_K)$ → `unifSimplex K`: normalized Lebesgue measure on the free coordinates $(p_1,\dots,p_{K-1})$, pushed to $\Delta_K$; reason: the uniform distribution on the simplex, as in the proof of Lemma 3.3 (App. A.1)
-- source:
--   Rivkin, Okoroafor, Kim, The Sample Complexity of Multi-Class Omniprediction, STOC 2027 submission (manuscript sha256 135d9904…), p. 26, Lemma 3.5 (proof: p. 55, App. A.1)

import Mathlib
import Definitions.Def_MultiOmniRate_Lipschitz_Setting
import Definitions.Def_MultiOmniRate_Lipschitz_OmniErrors
import Definitions.Def_MultiOmniRate_Lipschitz_Smoothing

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace MultiOmniRate.Lipschitz

theorem lemma_3_5 {K : ℕ} [NeZero K] (hK : 2 ≤ K) {X A : Type*} [MeasurableSpace X]
    [MeasurableSpace A] (L : Set (BRLoss K A)) (hL : ∀ ℓ ∈ L, ℓ.IsMeasurable)
    (H : Set (X → A)) (hH : ∀ h ∈ H, Measurable h) (hHne : H.Nonempty)
    (D : Measure (X × Fin K)) [IsProbabilityMeasure D] :
    (∀ (κ : Kernel X (Simplex K × Simplex K)) [IsMarkovKernel κ],
      HypOI L H D (Kernel.map κ Prod.fst) ≤ HypOI L H D (Kernel.map κ Prod.snd) +
        ∫ ω, l1 ((ω.2.1 : Fin K → ℝ) - (ω.2.2 : Fin K → ℝ)) ∂(D ⊗ₘ Kernel.prodMkRight (Fin K) κ)) ∧
    (∀ (q : Kernel X (Simplex K)) [IsMarkovKernel q] (r : ℝ), 0 < r → r ≤ 1 / 2 →
      HypOI L H D (smoothKernel r q) ≤ HypOI L H D q + 2 * r) := by sorry

end MultiOmniRate.Lipschitz
