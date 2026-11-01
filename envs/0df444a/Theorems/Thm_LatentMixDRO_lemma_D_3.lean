-- Prove2me | Theorems.Thm_LatentMixDRO_lemma_D_3
-- name    : LatentMixDRO.lemma_D_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:25:56.826992+00:00
-- url     : https://prove2.me/theorems/63513dd3-9df5-4a38-8fe1-a99c2aafef7b
-- title:
--   Lemma D.3 — concentration of the Wasserstein distance (corrected: constants depend on $R$)
-- statement:
--   Let $p\in(1,2]$ with $p-1<(d+1)/2$ and $R\in\mathbb R$. There are constants $c_1,c_2>0$ depending only on $d,p,R$ such that for every set $S\subset\mathbb R^d\times\mathbb R$ of Euclidean diameter at most $R$, every law $P$ carried by $S$, every $n\ge1$ and every $t>0$,
--
--   $$
--   \mathbb P\big(W_{p-1}(P,\widehat P_n)\ge t\big)\le c_1\exp\big(-c_2\,n\,(t^{\frac{d+1}{p-1}}\wedge t^2)\big).
--   $$
--
--   This supplies the rate $n^{-(p-1)/(d+1)}$ in the main theorem.
--
--   **Formalization Note** The left side is the outer measure of the event under the product measure, so no measurability of the distance is needed. The event contains the clause that the sample lies in $S$, which holds almost surely.
--
--   Differences from the source:
--   - correction: constants depending on $M,d,p$ → constants depending on $d,p,R$, chosen before $S,P,n,t$; reason: the printed form is false: for $P=\frac12\delta_0+\frac12\delta_{Re_1}$, $n$ odd and $R^{p-1}\ge2n$, $W_{p-1}\ge1$ always while $c_1e^{-c_2n}<1$ for large $n$; $M$ does not occur in the lemma
--   - generalization: $P$ on $\mathcal X\times\mathcal Y$ with $\operatorname{diam}\mathcal X+\operatorname{diam}\mathcal Y\le R$ → $P$ on any $S\subset\mathbb R^d\times\mathbb R$ of `dist2`-diameter at most $R$; reason: $S=\mathcal X\times\mathcal Y$ is an instance
--   - encoding: $\mathbb P(W\ge t)$ → outer measure of $\{\forall i,\ \omega_i\in S\}\cap\{W\ge t\}$; reason: the first event is almost sure, and it keeps the supremum defining $W$ finite
-- source:
--   Duchi, Hashimoto & Namkoong, Distributionally Robust Losses for Latent Covariate Mixtures, arXiv:2007.13982v2, Lemma D.3, p.39

import Mathlib
import Definitions.Def_LatentMixDRO_dist2
import Definitions.Def_LatentMixDRO_holderDev

open MeasureTheory

namespace LatentMixDRO

/-- Lemma D.3 (corrected: constants depend on `R`, not `M`): concentration of the Wasserstein distance.
For `p ∈ (1, 2]` and `p - 1 < (d + 1)/2`, and every `t > 0`,
`ℙ(W_{p-1}(P, P̂_n) ≥ t) ≤ c₁ exp(-c₂ n (t^{(d+1)/(p-1)} ∧ t²))`, with `c₁, c₂ > 0` depending on `d, p, R`,
for every law `P` on a set `S ⊂ ℝ^d × ℝ` of Euclidean diameter at most `R`.

Duchi, Hashimoto & Namkoong, arXiv:2007.13982v2, Lemma D.3, p.39 (citing Fournier and Guillin).

**Formalization Note.** `∃ c₁ c₂` stands before `S`, `P`, `n`, `t`, so the constants are uniform in them.
With constants independent of `R` the lemma is false (`P = ½δ₀ + ½δ_{R e₁}`, `n` odd, `R^{p-1} ≥ 2n`:
`W ≥ 1` always, against `c₁e^{-c₂n}` at `t = 1`). The lemma does not involve `M`. The bound is on the
outer measure of the event, so no measurability of `holderDev` is needed; `∀ i, ω i ∈ S` holds almost
surely and keeps the supremum in `holderDev` honest. -/
theorem lemma_D_3 (d : ℕ) (p R : ℝ) (hp : 1 < p) (hp2 : p ≤ 2)
    (hdim : p - 1 < ((d : ℝ) + 1) / 2) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ (S : Set (EuclideanSpace ℝ (Fin d) × ℝ)) (P : Measure (EuclideanSpace ℝ (Fin d) × ℝ))
        [IsProbabilityMeasure P],
        (∀ u ∈ S, ∀ u' ∈ S, dist2 u u' ≤ R) → (∀ᵐ u ∂P, u ∈ S) →
        ∀ n : ℕ, 1 ≤ n → ∀ t : ℝ, 0 < t →
          Measure.pi (fun _ : Fin n => P) {ω | (∀ i, ω i ∈ S) ∧ t ≤ holderDev S (p - 1) ω P}
            ≤ ENNReal.ofReal
                (c₁ * Real.exp (-(c₂ * (n : ℝ) * min (t ^ (((d : ℝ) + 1) / (p - 1))) (t ^ 2)))) := by sorry

end LatentMixDRO
