-- Prove2me | Theorems.Thm_LipStableCA_claim_4_10
-- name    : LipStableCA.claim_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:53:35.376332+00:00
-- url     : https://prove2.me/theorems/fb18e293-fa21-429b-be35-976cabb1d8a1
-- title:
--   Claim 4.10 — the selected index under a pointwise increase
-- statement:
--   With the notation of Observation 4.7, let $u,z\in U$ with $u_i(B)\le z_i(B)$ for every bundle $B$. Then, for the discounts of Mechanism 2,
--   $$\Pr\bigl[J(u,a)\ne J(z,a)\bigr]\le\frac m\epsilon\sum_{j=1}^R\log\frac{z_i(B_j)}{u_i(B_j)}\;p_j(z)^{1-1/m},$$
--   where $p_j(z)=\Pr[J(z,a)=j]$.
--
--   It is the step of Lemma 4.8 that compares a profile with the pointwise maximum of the two given ones.
--
--   Differences from the source:
--   - encoding: $m,n\ge 1$ throughout (§5 says so; Mechanism 2 has $U^{1/m}$) → the hypothesis `1 ≤ m`; reason: the paper's standing setting; excludes only the empty item set
--   - encoding: a total order on $\mathcal A$ fixed before the reports are seen → an explicit `LinearOrder` parameter, for every order; reason: Lean convention; same instances
--   - encoding: Pr over the seed of Mechanism 2 → the law `discountMeasure` of the independent uniforms $U_{i,B}$; reason: the discounts are functions of $U$; the coins do not enter these events
--   - encoding: the sum over $j\in[R]$ → the sum over the bundles $B\in\mathcal B$; reason: the enumeration plays no role
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Claim 4.10, p.16

import Definitions.Def_LipStableCA_discountIndex

namespace LipStableCA

/-- **Claim 4.10.** Afshinmehr, Koutsoupias, *Lipschitz Stable Combinatorial Auctions*, STOC 2027 submission (manuscript sha256 c5e4c53f…), p.16. **Formalization Note.** the hypothesis `1 ≤ m`: the paper's standing setting; excludes only the empty item set. an explicit `LinearOrder` parameter, for every order: Lean convention; same instances. the law `discountMeasure` of the independent uniforms `U_{i,B}`: the discounts are functions of `U`; the coins do not enter these events. the sum over the bundles `B∈𝓑`: the enumeration plays no role. -/
theorem claim_4_10 {n m : ℕ} (hm : 1 ≤ m) (ord : LinearOrder (Alloc n m)) {ϵ : ℝ} (h0 : 0 < ϵ)
    (h1 : ϵ < 1) (i : Fin n) (v : Profile n m) (𝓑 : Finset (Finset (Fin m))) (u z : Profile n m)
    (hu : InPattern v i 𝓑 u) (hz : InPattern v i 𝓑 z) (hle : ∀ B, u i B ≤ z i B) :
    (discountMeasure n m).real
        {U | selectedIndex ord i 𝓑 (discount ϵ U) u ≠ selectedIndex ord i 𝓑 (discount ϵ U) z} ≤
      (m : ℝ) / ϵ * ∑ B ∈ 𝓑, Real.log (z i B / u i B) *
        ((discountMeasure n m).real {U | selectedIndex ord i 𝓑 (discount ϵ U) z = some B}) ^
          (1 - 1 / (m : ℝ)) := by sorry

end LipStableCA
