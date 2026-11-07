-- Prove2me | Theorems.Thm_LipStableCA_lemma_5_6
-- name    : LipStableCA.lemma_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:54:43.582779+00:00
-- url     : https://prove2.me/theorems/a5b2017b-8ff4-44f2-93a8-8a68d1e2625e
-- title:
--   Lemma 5.6 — few bidders receive their hidden target
-- statement:
--   Let $(S,p)$ be a universally truthful mechanism with $\mathrm{Lip}(S)<\infty$. In the setting of Observation 5.5, for a seed $\omega$ let $C(\omega)$ be the number of pairs $(i,Y)$ of an active bidder $i\le q$ and a tuple $Y\in\mathcal Y$ such that $Y_i\subseteq S_i(v^Y;\omega)$. Then, for almost every seed $\omega$,
--   $$C(\omega)\le\bigl(3+q\,2^{-k}\bigr)\,|\mathcal Y|.$$
--
--   Since a bidder's offer does not depend on her own target, she can seldom receive it.
--
--   Differences from the source:
--   - encoding: the paper does not name a σ-algebra on the seed space → measurability of the rule stated as a clause or a hypothesis; reason: this is what makes the allocation law meaningful (paper.md decision 3)
--   - encoding: $qk\le m/2$ → `2 * (q * k) ≤ m`; reason: same condition over the naturals
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Lemma 5.6, p.24

import Definitions.Def_LipStableCA_targetProfile
import Definitions.Def_LipStableCA_IsLipschitz
open MeasureTheory

namespace LipStableCA

/-- **Lemma 5.6.** Afshinmehr, Koutsoupias, *Lipschitz Stable Combinatorial Auctions*, STOC 2027 submission (manuscript sha256 c5e4c53f…), p.24. **Formalization Note.** measurability of the rule stated as a clause or a hypothesis: this is what makes the allocation law meaningful (paper.md decision 3). `2 * (q * k) ≤ m`: same condition over the naturals. -/
theorem lemma_5_6 {n m q k : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (M : Mechanism n m Ω) (hM : M.Measurable) (hUT : M.IsUT μ)
    (hLip : ∃ K, IsLipschitz (M.law μ) K) (hq : 1 ≤ q) (hqn : q ≤ n) (hk : 1 ≤ k)
    (hqk : 2 * (q * k) ≤ m) :
    ∀ᵐ ω ∂μ, (targetCount M hqn k ω : ℝ) ≤
      (3 + (q : ℝ) * (2 : ℝ) ^ (-(k : ℤ))) * ((targetTuples q k m).card : ℝ) := by sorry

end LipStableCA
