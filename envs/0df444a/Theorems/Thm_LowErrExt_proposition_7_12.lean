-- Prove2me | Theorems.Thm_LowErrExt_proposition_7_12
-- name    : LowErrExt.proposition_7_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:54:14.044671+00:00
-- url     : https://prove2.me/theorems/650aad02-8049-4bbc-a584-1c993d1b17fd
-- title:
--   Proposition 7.12 — IP extracts from mixing sources
-- statement:
--   Let $d,q_i,p_i$ be positive integers with $p_i\mid q_i$, let $\mathrm{IP}$ be the inner product of Definition 7.11, and let $2^n:=\prod_i q_i$. Let $t_1,t_2\ge0$ be integers and $\mathbf X$, $\mathbf Y$ independent sources on $\prod_i\mathbb Z_{q_i}$ and $\prod_i\mathbb Z_{p_i}$ with
--   $$H_2[2^{t_1-1}\mathbf X-2^{t_1-1}\mathbf X]\ge k_1,\qquad H_2[2^{t_2-1}\mathbf Y-2^{t_2-1}\mathbf Y]\ge k_2 .$$
--   Then
--   $$\mathbb E_{x\sim\mathbf X}\big[|\mathbb E[\mathrm{IP}(x,\mathbf Y)]|\big]\le 2^{(n-k_1-k_2)/2^{t_1+t_2+2}}\quad\text{and}\quad \mathbb E_{y\sim\mathbf Y}\big[|\mathbb E[\mathrm{IP}(\mathbf X,y)]|\big]\le 2^{(n-k_1-k_2)/2^{t_1+t_2+2}} .$$
--
--   This is Bourgain's extractor over products of cyclic groups.
--
--   Differences from the source:
--   - encoding: positive integers d, q_i, p_i → 0 < d and NeZero (q i), NeZero (p i); reason: same instances
--   - encoding: 2^n := ∏ q_i → n = log₂ ∏ q_i, a real number; reason: same quantity
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), Proposition 7.12, p.54 (proved as Proposition 7.28, p.70)

import Mathlib
import Definitions.Def_LowErrExt_H2
import Definitions.Def_LowErrExt_iterDiff
import Definitions.Def_LowErrExt_ipC
import Definitions.Def_LowErrExt_strongBias

namespace LowErrExt

/-- **Proposition 7.12 (IP extracts from mixing sources).**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Proposition 7.12, p.54 (proved as Proposition 7.28, p.70): "Let IP : (Zq1 × · · · × Zqd) ×
(Zp1 × · · · × Zpd) → C× be the function in Definition 7.11, and let 2^n := ∏i qi. For any
t1, t2 ∈ N≥0 and independent sources X ∼ Zq1 × · · · × Zqd and Y ∼ Zp1 × · · · × Zpd with
H2[2^{t1−1}X − 2^{t1−1}X] ≥ k1 and H2[2^{t2−1}Y − 2^{t2−1}Y] ≥ k2,
E_{x∼X}[|E[IP(x, Y)]|] ≤ 2^{(n−k1−k2)/2^{t1+t2+2}}, and E_{y∼Y}[|E[IP(X, y)]|] ≤ 2^{(n−k1−k2)/2^{t1+t2+2}}."

**Formalization Note.** `d, qᵢ, pᵢ` are positive integers (`NeZero`) with `pᵢ ∣ qᵢ`
(Definition 7.11); `n = log₂ ∏ qᵢ` is real; `t = 0` means the source itself. -/
theorem proposition_7_12 {d : ℕ} (hd : 0 < d) (q p : Fin d → ℕ) [∀ i, NeZero (q i)]
    [∀ i, NeZero (p i)] (hpq : ∀ i, p i ∣ q i) (t₁ t₂ : ℕ) (k₁ k₂ : ℝ)
    (X : PMF (∀ i, ZMod (q i))) (Y : PMF (∀ i, ZMod (p i)))
    (hX : k₁ ≤ H2 (iterDiff t₁ X)) (hY : k₂ ≤ H2 (iterDiff t₂ Y)) :
    strongBiasLeft X Y (ipC q p) ≤
        (2 : ℝ) ^ ((Real.logb 2 (∏ i, (q i : ℝ)) - k₁ - k₂) / (2 : ℝ) ^ (t₁ + t₂ + 2)) ∧
      strongBiasRight X Y (ipC q p) ≤
        (2 : ℝ) ^ ((Real.logb 2 (∏ i, (q i : ℝ)) - k₁ - k₂) / (2 : ℝ) ^ (t₁ + t₂ + 2)) := by sorry

end LowErrExt
