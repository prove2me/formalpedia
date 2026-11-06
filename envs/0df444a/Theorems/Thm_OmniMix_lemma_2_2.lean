-- Prove2me | Theorems.Thm_OmniMix_lemma_2_2
-- name    : OmniMix.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:39:49.381407+00:00
-- url     : https://prove2.me/theorems/4383c03b-6c07-4ee9-b26e-e8afe1dd6d4e
-- title:
--   Lemma 2.2 — binary EVI on a closed interval
-- statement:
--   Let $0\le\delta<1/2$, $I_\delta=[\delta,1-\delta]$, and let $G:I_\delta\to\mathbb R$ satisfy $1+G(p)(y-p)\ge0$ for all $p\in I_\delta$ and $y\in\{0,1\}$. Let $\epsilon>\delta/(1-\delta)$.
--
--   1. There is a distribution $D$ on $I_\delta$ with at most three support points such that
--   $$
--   \mathbb E_{P\sim D}\big[G(P)(y-P)\big]\le\epsilon\qquad\text{for both }y\in\{0,1\}.
--   $$
--   2. If $\delta>0$, then for every finite grid $\Gamma\subseteq I_\delta$ that contains $\delta$ and $1-\delta$ and whose consecutive points are at most $\delta$ apart, such a $D$ (with at most three support points) exists with support in $\Gamma$.
--
--   This is the per-round forecast step of Algorithm 2: it turns the test function $G_t$ into a forecast that no outcome can exploit by more than $\epsilon_t$.
--
--   Differences from the source:
--   - reading: D may be supported on any such grid → a D supported in the grid with at most three support points; reason: the proof (p.35) applies Carathéodory to a distribution on the grid, keeping both properties
--   - encoding: G : I_δ → ℝ → G : [0,1] → ℝ, with the hypothesis only on I_δ; reason: values outside I_δ never enter
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, Lemma 2.2, p.10 (PDF p.12); proof App. C, pp.34–35

import Mathlib
import Definitions.Def_OmniMix_FinDist_expectR
import Definitions.Def_OmniMix_Idelta
import Definitions.Def_OmniMix_outVal

namespace OmniMix

/-- **Lemma 2.2 (Binary EVI on a closed interval).** Liu–Luo–Ratliff, arXiv:2610.41023, §2, p.10 (proof App. C, pp.34–35):
"For every `0 ≤ δ < 1/2`, every `G : I_δ → ℝ` satisfying `1 + G(p)(y − p) ≥ 0` for all `p ∈ I_δ` and
`y ∈ {0, 1}`, and every `ϵ > δ/(1 − δ)`, there is a distribution `D` on `I_δ` with at most three
support points such that `E_{P∼D}[G(P)(y − P)] ≤ ϵ, ∀y ∈ {0, 1}`. When `δ > 0`, `D` may be supported
on any finite grid containing the endpoints of `I_δ` whose adjacent gaps are at most `δ`."

**Formalization Note.** `G` is given on all of `[0,1]`; only its values on `I_δ` enter. A grid is
a finite `Γ ⊆ I_δ` containing `δ` and `1 − δ` in which consecutive points (no grid point strictly
between them) are at most `δ` apart. The second clause gives a `D` on `Γ` that also has at most
three support points (the proof's Carathéodory step, p.35, keeps the support inside `Γ`). -/
theorem lemma_2_2 (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (G : unitInterval → ℝ)
    (hG : ∀ p : unitInterval, (p : ℝ) ∈ Idelta δ → ∀ y : Bool, 0 ≤ 1 + G p * (outVal y - p))
    (ε : ℝ) (hε : δ / (1 - δ) < ε) :
    (∃ D : FinDist, (∀ P ∈ D.wt.support, (P : ℝ) ∈ Idelta δ) ∧ D.wt.support.card ≤ 3 ∧
      ∀ y : Bool, D.expectR (fun P => G P * (outVal y - P)) ≤ ε) ∧
    (0 < δ → ∀ Γ : Finset unitInterval, (∀ a ∈ Γ, (a : ℝ) ∈ Idelta δ) →
      (∃ a ∈ Γ, (a : ℝ) = δ) → (∃ a ∈ Γ, (a : ℝ) = 1 - δ) →
      (∀ a ∈ Γ, ∀ b ∈ Γ, a < b → (∀ c ∈ Γ, ¬ (a < c ∧ c < b)) → (b : ℝ) - a ≤ δ) →
      ∃ D : FinDist, (∀ P ∈ D.wt.support, P ∈ Γ) ∧ D.wt.support.card ≤ 3 ∧
        ∀ y : Bool, D.expectR (fun P => G P * (outVal y - P)) ≤ ε) := by sorry

end OmniMix
