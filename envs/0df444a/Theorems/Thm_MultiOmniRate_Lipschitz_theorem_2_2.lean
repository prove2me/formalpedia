-- Prove2me | Theorems.Thm_MultiOmniRate_Lipschitz_theorem_2_2
-- name    : MultiOmniRate.Lipschitz.theorem_2_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:23:41.810192+00:00
-- url     : https://prove2.me/theorems/845681ea-90e7-429d-ac0d-53c283e46f3e
-- title:
--   Theorem 2.2 — Loss OI reduction: $\mathrm{OmniReg}_{\mathcal L,\mathcal H}\le\mathrm{DecOI}_{\mathcal L}+\mathrm{HypOI}_{\mathcal L,\mathcal H}$
-- statement:
--   Fix $K\ge2$ labels, a measurable context space $\mathcal X$, a measurable action space $\mathcal A$, a class $\mathcal L$ of losses $\ell:\mathcal A\times\mathcal Y\to[-1,1]$, each with a fixed measurable best response $\mathrm{BR}_\ell$, and a nonempty class $\mathcal H$ of measurable benchmark rules $h:\mathcal X\to\mathcal A$. For every distribution $\mathcal D$ on $\mathcal X\times\mathcal Y$ and every randomized predictor $p$,
--   $$\mathrm{OmniReg}_{\mathcal L,\mathcal H}(p)\ \le\ \mathrm{DecOI}_{\mathcal L}(p)+\mathrm{HypOI}_{\mathcal L,\mathcal H}(p).$$
--   Here, with $(x,y)\sim\mathcal D$, the reported vector $p(x)$ and a modeled label $\tilde y\sim p(x)$: $\mathrm{OmniReg}=\sup_{\ell,h}\mathbb E[\ell(\mathrm{BR}_\ell(p(x)),y)-\ell(h(x),y)]$, $\mathrm{DecOI}=\sup_\ell|\mathbb E[\ell(\mathrm{BR}_\ell(p(x)),y)-\ell(\mathrm{BR}_\ell(p(x)),\tilde y)]|$ and $\mathrm{HypOI}=\sup_{\ell,h}|\mathbb E[\ell(h(x),y)-\ell(h(x),\tilde y)]|$.
--
--   This is the reduction (from Gopalan et al.) that splits omniprediction into a calibration-type condition and a multiaccuracy-type condition; every upper bound of the paper goes through it.
--
--   Differences from the source:
--   - encoding: labels $\mathcal Y=\{0,\dots,K-1\}$ → `Fin K`, with `[NeZero K]` (implied by $K\ge2$) so that label $0$ exists; reason: relabeling; same instances
--   - encoding: randomized predictor $\mathcal X\to\Delta(\Delta_K)$; modeled label $\tilde y\sim p(x)$ → Markov kernel `Kernel X (Simplex K)`; $\mathbb E_{\tilde y\sim a}\ell(\cdot,\tilde y)$ written as $\langle a,\ell(\cdot,\cdot)\rangle$; reason: footnote 3 (p. 19); the modeled-label expectation is exact
--   - reading: "we fix a measurable best response" (p. 19); benchmark rules $h$ → each $\ell\in\mathcal L$ is measurable in the action with measurable $\mathrm{BR}_\ell$ (`BRLoss.IsMeasurable`), each $h\in\mathcal H$ is measurable; reason: the paper's standing convention; it is what makes every expectation defined
--   - encoding: suprema over a loss class (empty class: $-\infty$) → real `⨆` over the class; every term is bounded by $2$ in absolute value, and the empty supremum is $0$; reason: an empty $\mathcal L$ makes every side $0$, which the inequality covers as the paper's convention does
-- source:
--   Rivkin, Okoroafor, Kim, The Sample Complexity of Multi-Class Omniprediction, STOC 2027 submission (manuscript sha256 135d9904…), p. 20, Theorem 2.2

import Mathlib
import Definitions.Def_MultiOmniRate_Lipschitz_Setting
import Definitions.Def_MultiOmniRate_Lipschitz_OmniErrors

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace MultiOmniRate.Lipschitz

theorem theorem_2_2 {K : ℕ} [NeZero K] (hK : 2 ≤ K) {X A : Type*} [MeasurableSpace X]
    [MeasurableSpace A] (L : Set (BRLoss K A)) (hL : ∀ ℓ ∈ L, ℓ.IsMeasurable)
    (H : Set (X → A)) (hH : ∀ h ∈ H, Measurable h) (hHne : H.Nonempty)
    (D : Measure (X × Fin K)) [IsProbabilityMeasure D]
    (p : Kernel X (Simplex K)) [IsMarkovKernel p] :
    OmniReg L H D p ≤ DecOI L D p + HypOI L H D p := by sorry

end MultiOmniRate.Lipschitz
