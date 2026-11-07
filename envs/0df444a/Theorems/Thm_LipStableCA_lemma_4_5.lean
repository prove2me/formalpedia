-- Prove2me | Theorems.Thm_LipStableCA_lemma_4_5
-- name    : LipStableCA.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:51:31.861193+00:00
-- url     : https://prove2.me/theorems/1cfe3395-918d-49ff-a222-5f93236f5c75
-- title:
--   Lemma 4.5 — the Lipschitz constant of Mechanism 2
-- statement:
--   For the random discount auction (Mechanism 2) with parameter $0<\epsilon<1$ and any fixed order on the allocations,
--   $$\mathrm{Lip}(S)\le\frac{2m^2(2^m-1)^{1/m}}{\epsilon}<\frac{4m^2}{\epsilon}.$$
--
--   Together with the welfare guarantee, it gives the upper bound of Theorem 4.11.
--
--   Differences from the source:
--   - encoding: $m,n\ge 1$ throughout (§5 says so; Mechanism 2 has $U^{1/m}$) → the hypothesis `1 ≤ m`; reason: the paper's standing setting; excludes only the empty item set
--   - encoding: a total order on $\mathcal A$ fixed before the reports are seen → an explicit `LinearOrder` parameter, for every order; reason: Lean convention; same instances
--   - encoding: the paper does not name a σ-algebra on the seed space → measurability of the rule stated as a clause or a hypothesis; reason: this is what makes the allocation law meaningful (paper.md decision 3)
--   - encoding: $\mathrm{Lip}(S)\le K$ → `IsLipschitz P K`; reason: the set of valid constants is closed, so the two are equivalent (paper.md decision 4)
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Lemma 4.5, p.15

import Definitions.Def_LipStableCA_randomDiscount
import Definitions.Def_LipStableCA_IsLipschitz

namespace LipStableCA

/-- **Lemma 4.5.** Afshinmehr, Koutsoupias, *Lipschitz Stable Combinatorial Auctions*, STOC 2027 submission (manuscript sha256 c5e4c53f…), p.15. **Formalization Note.** the hypothesis `1 ≤ m`: the paper's standing setting; excludes only the empty item set. an explicit `LinearOrder` parameter, for every order: Lean convention; same instances. measurability of the rule stated as a clause or a hypothesis: this is what makes the allocation law meaningful (paper.md decision 3). `IsLipschitz P K`: the set of valid constants is closed, so the two are equivalent (paper.md decision 4). -/
theorem lemma_4_5 {n m : ℕ} (hm : 1 ≤ m) (ord : LinearOrder (Alloc n m)) {ϵ : ℝ} (h0 : 0 < ϵ)
    (h1 : ϵ < 1) :
    (randomDiscount ord ϵ).Measurable ∧
    IsLipschitz ((randomDiscount ord ϵ).law (discountSeedMeasure n m))
      (2 * (m : ℝ) ^ 2 * ((2 : ℝ) ^ m - 1) ^ (1 / (m : ℝ)) / ϵ) ∧
    2 * (m : ℝ) ^ 2 * ((2 : ℝ) ^ m - 1) ^ (1 / (m : ℝ)) / ϵ < 4 * (m : ℝ) ^ 2 / ϵ := by sorry

end LipStableCA
