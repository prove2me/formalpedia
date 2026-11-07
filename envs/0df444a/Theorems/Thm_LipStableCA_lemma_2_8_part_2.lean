-- Prove2me | Theorems.Thm_LipStableCA_lemma_2_8_part_2
-- name    : LipStableCA.lemma_2_8_part_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:48:31.400776+00:00
-- url     : https://prove2.me/theorems/5ce957d7-8682-41be-8fc3-84cbe1c47631
-- title:
--   Lemma 2.8, part 2 — EMD is jointly convex under mixtures
-- statement:
--   Let $\lambda$ be a random variable on a probability space, and let $\mu^\lambda,\nu^\lambda$ be distributions on the set of allocations whose masses depend measurably on $\lambda$. Then
--   $$\mathrm{EMD}\bigl(\mathbb E_\lambda[\mu^\lambda],\,\mathbb E_\lambda[\nu^\lambda]\bigr)\le\mathbb E_\lambda\bigl[\mathrm{EMD}(\mu^\lambda,\nu^\lambda)\bigr].$$
--
--   It reduces every Lipschitz bound for a randomized rule to a bound conditional on part of the seed.
--
--   Differences from the source:
--   - encoding: distributions on $\mathcal A$ → real mass functions (`IsLaw`); reason: $\mathcal A$ is finite; same objects
--   - encoding: $\mathbb E_\lambda[\mathrm{EMD}]$ → the integrability of $\lambda\mapsto\mathrm{EMD}(\mu^\lambda,\nu^\lambda)$ as an extra conclusion; reason: it makes the Bochner integral the paper's expectation; EMD is bounded and measurable on laws
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Lemma 2.8, part 2, p.8

import Definitions.Def_LipStableCA_emd
open MeasureTheory

namespace LipStableCA

/-- **Lemma 2.8, part 2.** Afshinmehr, Koutsoupias, *Lipschitz Stable Combinatorial Auctions*, STOC 2027 submission (manuscript sha256 c5e4c53f…), p.8. **Formalization Note.** real mass functions (`IsLaw`): `A` is finite; same objects. the integrability of `λ↦EMD(µ^λ,ν^λ)` as an extra conclusion: it makes the Bochner integral the paper's expectation; EMD is bounded and measurable on laws. -/
theorem lemma_2_8_part_2 {n m : ℕ} {Λ : Type*} [MeasurableSpace Λ] (ρ : Measure Λ)
    [IsProbabilityMeasure ρ] (μ ν : Λ → Alloc n m → ℝ) (hμ : ∀ l, IsLaw (μ l)) (hν : ∀ l, IsLaw (ν l))
    (hμm : ∀ T, Measurable fun l => μ l T) (hνm : ∀ T, Measurable fun l => ν l T) :
    Integrable (fun l => emd (μ l) (ν l)) ρ ∧
      emd (fun T => ∫ l, μ l T ∂ρ) (fun T => ∫ l, ν l T ∂ρ) ≤ ∫ l, emd (μ l) (ν l) ∂ρ := by sorry

end LipStableCA
