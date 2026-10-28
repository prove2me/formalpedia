-- Prove2me | Theorems.Thm_GIGnBounds_Tail_lemma_9
-- name    : GIGnBounds.Tail.lemma_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T01:21:39.843406+00:00
-- url     : https://prove2.me/theorems/ba7c27c6-860c-4ae2-8cdf-f8080b052b14
-- title:
--   Lemma 9 (Kingman) — $P(\sup_{k\ge0}(ck-\sum_{i\le k}Z_i)\ge x)\le e^{-\theta x}$
-- statement:
--   Let $Z_1,Z_2,\dots$ be i.i.d. nonnegative random variables with $\mathbb E[Z_1]=1$, let $c\in(0,1)$, and suppose $\mathbb E[\exp(\theta(c-Z_1))]\le1$ for some $\theta>0$.
--
--   **Lemma 9** (Kingman). For all $x>0$,
--
--   $$\mathbb P\Big(\sup_{k\ge0}\Big(c\,k-\sum_{i=1}^kZ_i\Big)\ge x\Big)\le e^{-\theta x}.$$
--
--   This is the exponential tail bound for the supremum of a random walk with negative drift, i.e. for the waiting time of a stable single-server queue.
--
--   **Formalization Note.** The page prints $Z_k$ inside the supremum; the object meant (and used through Lemma 8) is the partial sum $\sum_{i=1}^kZ_i$, which is what is stated. The sequence is indexed from $0$, and the supremum is in the extended reals.
-- source:
--   Li and Goldberg, Simple and explicit bounds for multi-server queues with 1/(1−ρ) scaling, arXiv:1706.04628v3, p. 33, Lemma 9

import Mathlib
import Definitions.Def_GIGnBounds_Tail_Setting

open MeasureTheory ProbabilityTheory

namespace GIGnBounds.Tail

/-- **Lemma 9** (Kingman; Li–Goldberg, arXiv:1706.04628v3, p. 33). Let `Z₁, Z₂, …` (here `Z 0, Z 1, …`)
be i.i.d. nonnegative with `E[Z₁] = 1`, `c ∈ (0, 1)`, and `E[exp(θ(c − Z₁))] ≤ 1` for some `θ > 0`.
Then `P(sup_{k≥0} (c k − Σ_{i=1}^k Z_i) ≥ x) ≤ exp(−θ x)` for all `x > 0`. (The page prints `Z_k`
for the partial sum `Σ_{i=1}^k Z_i`.) -/
theorem lemma_9 (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν0 : ν (Set.Iio 0) = 0)
    (hν1 : ∫ z, z ∂ν = 1) (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (θ : ℝ) (hθ : 0 < θ)
    (hmgf : ∫ z, Real.exp (θ * (c - z)) ∂ν ≤ 1)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℕ → Ω → ℝ) (hZ : IsIIDSeq P Z ν) (x : ℝ) (hx : 0 < x) :
    P.real {ω | (x : EReal) ≤ ⨆ k : ℕ, ((c * k - ∑ i ∈ Finset.range k, Z i ω : ℝ) : EReal)} ≤
      Real.exp (-θ * x) := by sorry

end GIGnBounds.Tail
