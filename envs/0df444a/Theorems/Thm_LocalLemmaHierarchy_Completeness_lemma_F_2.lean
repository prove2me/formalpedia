-- Prove2me | Theorems.Thm_LocalLemmaHierarchy_Completeness_lemma_F_2
-- name    : LocalLemmaHierarchy.Completeness.lemma_F_2
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-10T00:18:28.506892+00:00
-- url     : https://prove2.me/theorems/d1cebec8-a0c3-43cb-b48d-b7c612af6d17
-- title:
--   Lemma F.2 — two weighted geometric means: $\mathrm{GM}_\alpha(z)+\mathrm{GM}_\beta(1-z)\le 1+\sum(\sqrt{\alpha_i}-\sqrt{\beta_i})^2$
-- statement:
--   Let $\alpha,\beta$ be probability vectors on the same finite index set $I$. For every $z\in[0,1]^I$,
--   $$\mathrm{GM}_\alpha(z)+\mathrm{GM}_\beta(1-z)\le1+\frac12\sum_{i:\alpha_i+\beta_i>0}\frac{(\alpha_i-\beta_i)^2}{\alpha_i+\beta_i}\qquad(F.3)$$
--   $$\le1+\sum_i(\sqrt{\alpha_i}-\sqrt{\beta_i})^2.\qquad(F.4)$$
--
--   Differences from the source:
--   - encoding: GM_α(z) = ∏ z_i^{α_i}, omitting factors with zero exponent and interpreting boundary values by continuity → ∏ i, z i ^ α i with Real.rpow; reason: Real.rpow has 0^0 = 1 (zero exponents contribute 1) and 0^a = 0 for a > 0, the continuous boundary value
-- source:
--   Achlioptas, Kritharidis and Zampetakis, A Complete Hierarchy of Local Lemmas, STOC 2027 submission (manuscript sha256 bc1388b0…a434b961), Lemma F.2, printed p. 36 (PDF p. 38); proof printed pp. 36–37 (PDF pp. 38–39)

import Mathlib
import Definitions.Def_LocalLemmaHierarchy_Completeness_Weights

namespace LocalLemmaHierarchy.Completeness

/-- **Lemma F.2 (Two weighted geometric means)**, printed p. 36 / PDF 38 (proof printed 36–37).
For probability vectors `α, β` on the same finite index set and every `z ∈ [0,1]^I`,
`GM_α(z) + GM_β(1 − z) ≤ 1 + ½ ∑_{i : α_i + β_i > 0} (α_i − β_i)²/(α_i + β_i)` (F.3)
`≤ 1 + ∑_i (√α_i − √β_i)²` (F.4). -/
theorem lemma_F_2 {ι : Type} [Fintype ι] (α β : ι → ℝ) (hα : ∀ i, 0 ≤ α i)
    (hα1 : ∑ i, α i = 1) (hβ : ∀ i, 0 ≤ β i) (hβ1 : ∑ i, β i = 1) (z : ι → ℝ)
    (hz : ∀ i, 0 ≤ z i ∧ z i ≤ 1) :
    geomMean α z + geomMean β (fun i => 1 - z i) ≤
        1 + (1 / 2) * ∑ i ∈ Finset.univ.filter (fun i => 0 < α i + β i),
          (α i - β i) ^ 2 / (α i + β i) ∧
    1 + (1 / 2) * ∑ i ∈ Finset.univ.filter (fun i => 0 < α i + β i),
          (α i - β i) ^ 2 / (α i + β i) ≤
        1 + ∑ i, (Real.sqrt (α i) - Real.sqrt (β i)) ^ 2 := by sorry

end LocalLemmaHierarchy.Completeness
