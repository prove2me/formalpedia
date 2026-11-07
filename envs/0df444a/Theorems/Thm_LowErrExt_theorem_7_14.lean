-- Prove2me | Theorems.Thm_LowErrExt_theorem_7_14
-- name    : LowErrExt.theorem_7_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:54:53.525936+00:00
-- url     : https://prove2.me/theorems/36ce146b-409c-4430-ae16-7c1843df4b78
-- title:
--   Theorem 7.14 — IP extracts from spread sources
-- statement:
--   Let $m\ge2$. There are constants $C,C'\ge1$ depending only on $m$ such that the following holds. Let $d,q_i,p_i$ be positive integers with $p_i\mid q_i$ and $q_i\mid m$, let $\mathrm{IP}$ be the inner product of Definition 7.11 and $2^n:=\prod_iq_i$. Let $\mathbf X$, $\mathbf Y$ be independent sources on $\prod_i\mathbb Z_{q_i}$, $\prod_i\mathbb Z_{p_i}$ such that $\mathbf X$ is $(r_1,k_1)_2$-spread in $\prod_i\mathbb Z_{q_i}$, $H_2[\mathbf Y]\ge k_2$, and $k_1\ge C$. Then
--   $$\mathbb E_{x\sim\mathbf X}\big[|\mathbb E[\mathrm{IP}(x,\mathbf Y)]|\big]\le 2^{\frac14(r_1-k_2)/(n/k_1)^{C'}}\quad\text{and}\quad\mathbb E_{y\sim\mathbf Y}\big[|\mathbb E[\mathrm{IP}(\mathbf X,y)]|\big]\le 2^{\frac14(r_1-k_2)/(n/k_1)^{C'}} .$$
--
--   No condition $n\ge k_1$ is needed (footnote 27). This is the third ingredient of Theorem 7.5.
--
--   Differences from the source:
--   - encoding: spreadness over all homomorphisms L out of G (Definition 6.2) → spreadness over the quotient maps G → G/K for subgroups K (IsSpread); reason: a homomorphism with kernel K is an injective map after π_K, so images and entropies agree (Observation 6.5's argument); same instances
--   - encoding: positive integers d, q_i, p_i; 2^n := ∏ q_i → 0 < d, NeZero (q i), NeZero (p i); n = log₂ ∏ q_i; reason: same instances
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), Theorem 7.14, pp.54–55

import Mathlib
import Definitions.Def_LowErrExt_H2
import Definitions.Def_LowErrExt_IsSpread
import Definitions.Def_LowErrExt_ipC
import Definitions.Def_LowErrExt_strongBias

namespace LowErrExt

/-- **Theorem 7.14 (IP extracts from spread sources).**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Theorem 7.14, pp.54–55: "Let IP : (Zq1 × · · · × Zqd) × (Zp1 × · · · × Zpd) → C× be the function in
Definition 7.11, let 2^n := ∏i qi, and let m ≥ 2 be an integer such that each qi|m. Then, for any
independent sources X ∼ Zq1 × · · · × Zqd and Y ∼ Zp1 × · · · × Zpd such that X is (r1, k1)2-spread in
Zq1 × · · · × Zqd and H2[Y] ≥ k2, and k1 ≥ C, it holds that
E_{x∼X}[|E[IP(x, Y)]|] ≤ 2^{¼(r1−k2)/(n/k1)^{C′}}, and E_{y∼Y}[|E[IP(X, y)]|] ≤ 2^{¼(r1−k2)/(n/k1)^{C′}}
for some constants C, C′ ≥ 1 depending only on m."

**Formalization Note.** The constants are chosen after `m` and before `d, q, p` and the sources.
Spreadness is in the whole group (`Set.univ`). `n ≥ k₁` is not assumed (footnote 27, p.55). -/
theorem theorem_7_14 (m : ℕ) (hm : 2 ≤ m) :
    ∃ C C' : ℝ, 1 ≤ C ∧ 1 ≤ C' ∧
      ∀ {d : ℕ} (q p : Fin d → ℕ) [∀ i, NeZero (q i)] [∀ i, NeZero (p i)], 0 < d →
        (∀ i, p i ∣ q i) → (∀ i, q i ∣ m) →
          ∀ (X : PMF (∀ i, ZMod (q i))) (Y : PMF (∀ i, ZMod (p i))) (r₁ k₁ k₂ : ℝ),
            IsSpread2 r₁ k₁ Set.univ X → k₂ ≤ H2 Y → C ≤ k₁ →
              strongBiasLeft X Y (ipC q p) ≤
                  (2 : ℝ) ^ (1 / 4 * (r₁ - k₂) / (Real.logb 2 (∏ i, (q i : ℝ)) / k₁) ^ C') ∧
                strongBiasRight X Y (ipC q p) ≤
                  (2 : ℝ) ^ (1 / 4 * (r₁ - k₂) / (Real.logb 2 (∏ i, (q i : ℝ)) / k₁) ^ C') := by sorry

end LowErrExt
