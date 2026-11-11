-- Prove2me | Theorems.Thm_MultiOmniRate_Lipschitz_proposition_2_5
-- name    : MultiOmniRate.Lipschitz.proposition_2_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:23:34.622701+00:00
-- url     : https://prove2.me/theorems/8ffdc7a9-9ba4-44c1-bcc7-8e221ce3ca2b
-- title:
--   Proposition 2.5 — $\mathrm{DecOI}_{\mathcal L}\le\mathrm{DecOI}_{\mathcal L_{\mathrm{All}}}=\mathrm{PCal}_K\le\mathrm{ECE}_1$
-- statement:
--   Fix $K\ge2$, a measurable context space $\mathcal X$, a distribution $\mathcal D$ on $\mathcal X\times\mathcal Y$ and a randomized predictor $p$. For every class $\mathcal L$ of bounded losses on a measurable action space $\mathcal A$ (each measurable in the action, with a fixed measurable best response),
--   $$\mathrm{DecOI}_{\mathcal L}(p)\ \le\ \mathrm{DecOI}_{\mathcal L_{\mathrm{All}}}(p)\ =\ \mathrm{PCal}_K(p)\ \le\ \mathrm{ECE}_1(p),$$
--   where $\mathcal L_{\mathrm{All}}$ is the class of all bounded decision losses with measurable best responses on arbitrary action spaces, $\mathrm{PCal}_K(p)=\sup_{\ell\in\mathcal L_{\mathrm{prop}}}|\mathbb E\langle\Delta\ell(p(x)),e_y-p(x)\rangle|$ and $\mathrm{ECE}_1(p)=\mathbb E\|\mathbb E[e_y-p(x)\mid p(x)]\|_1$.
--
--   Decision OI for every bounded loss class is therefore controlled by proper calibration, the quantity the decision learner of §3.4 targets.
--
--   **Formalization Note.** $\mathcal L_{\mathrm{All}}$ is `AllLoss.{u} K` with action spaces in the universe of $\mathcal A$, so that the first inequality is an inclusion of classes.
--
--   Differences from the source:
--   - encoding: labels $\mathcal Y=\{0,\dots,K-1\}$ → `Fin K`, with `[NeZero K]` (implied by $K\ge2$) so that label $0$ exists; reason: relabeling; same instances
--   - encoding: randomized predictor $\mathcal X\to\Delta(\Delta_K)$; modeled label $\tilde y\sim p(x)$ → Markov kernel `Kernel X (Simplex K)`; $\mathbb E_{\tilde y\sim a}\ell(\cdot,\tilde y)$ written as $\langle a,\ell(\cdot,\cdot)\rangle$; reason: footnote 3 (p. 19); the modeled-label expectation is exact
--   - reading: "we fix a measurable best response"; $\mathcal L_{\mathrm{prop}}$ members → every $\ell\in\mathcal L$ and every member of $\mathcal L_{\mathrm{All}}$ is measurable in the action with measurable best response; members of $\mathcal L_{\mathrm{prop}}$ are measurable in the action; reason: needed for the expectations in DecOI and PCal to be defined; the paper's standing convention
--   - encoding: $\mathcal L_{\mathrm{All}}$: arbitrary action spaces → `AllLoss.{u} K`: action spaces in a universe `u`, with a measurable structure; reason: $w_{\ell,r}$ and the Decision-OI term depend on $\ell$ only through $\ell^{\mathrm{pr}}$, which is itself a loss on $\Delta_K$, so every universe gives the same class
--   - encoding: $\mathrm{ECE}_1(p)=\mathbb E\|\mathbb E[e_y-p(x)\mid p(x)]\|_1=\sup_w|\mathbb E\langle w(p(x)),e_y-p(x)\rangle|$ → the first expression, with Mathlib `condExp` given the σ-algebra of the reported vector; reason: it is the definition; the supremum form is a derived identity
--   - encoding: suprema over a loss class (empty class: $-\infty$) → real `⨆` over the class; every term is bounded by $2$ in absolute value, and the empty supremum is $0$; reason: an empty $\mathcal L$ makes every side $0$, which the inequality covers as the paper's convention does
-- source:
--   Rivkin, Okoroafor, Kim, The Sample Complexity of Multi-Class Omniprediction, STOC 2027 submission (manuscript sha256 135d9904…), p. 22, Proposition 2.5 (with Definition 2.4 and ECE₁, p. 22)

import Mathlib
import Definitions.Def_MultiOmniRate_Lipschitz_Setting
import Definitions.Def_MultiOmniRate_Lipschitz_OmniErrors

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace MultiOmniRate.Lipschitz

theorem proposition_2_5.{u, v} {K : ℕ} [NeZero K] (hK : 2 ≤ K) {X : Type v} [MeasurableSpace X]
    {A : Type u} [MeasurableSpace A] (L : Set (BRLoss K A)) (hL : ∀ ℓ ∈ L, ℓ.IsMeasurable)
    (D : Measure (X × Fin K)) [IsProbabilityMeasure D]
    (p : Kernel X (Simplex K)) [IsMarkovKernel p] :
    DecOI L D p ≤ DecOIAll.{u} D p ∧ DecOIAll.{u} D p = PCal D p ∧ PCal D p ≤ ECE1 D p := by sorry

end MultiOmniRate.Lipschitz
