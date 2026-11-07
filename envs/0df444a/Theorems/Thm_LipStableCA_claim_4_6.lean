-- Prove2me | Theorems.Thm_LipStableCA_claim_4_6
-- name    : LipStableCA.claim_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:51:14.229614+00:00
-- url     : https://prove2.me/theorems/8a5e0c21-b991-43b4-aea8-0dc0ba4e2a43
-- title:
--   Claim 4.6 — the allocation law moves only when the selected allocation changes
-- statement:
--   For all profiles $v$ and $w$, the allocation laws of Mechanism 2 satisfy
--   $$\mathrm{EMD}(P_v,P_w)\le 2m\,\Pr\bigl[S^*(v,a)\ne S^*(w,a)\bigr],$$
--   where $S^*(u,a)$ is the allocation selected at the profile $u$ under the vector of discounts $a$, and the probability is over the discounts.
--
--   The delivery coins are integrated out, so the remaining work is about the discounts alone.
--
--   Differences from the source:
--   - encoding: $m,n\ge 1$ throughout (§5 says so; Mechanism 2 has $U^{1/m}$) → the hypothesis `1 ≤ m`; reason: the paper's standing setting; excludes only the empty item set
--   - encoding: a total order on $\mathcal A$ fixed before the reports are seen → an explicit `LinearOrder` parameter, for every order; reason: Lean convention; same instances
--   - encoding: Pr over the seed of Mechanism 2 → the law `discountMeasure` of the independent uniforms $U_{i,B}$; reason: the discounts are functions of $U$; the coins do not enter these events
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Claim 4.6, p.15

import Definitions.Def_LipStableCA_randomDiscount
import Definitions.Def_LipStableCA_emd

namespace LipStableCA

/-- **Claim 4.6.** Afshinmehr, Koutsoupias, *Lipschitz Stable Combinatorial Auctions*, STOC 2027 submission (manuscript sha256 c5e4c53f…), p.15. **Formalization Note.** the hypothesis `1 ≤ m`: the paper's standing setting; excludes only the empty item set. an explicit `LinearOrder` parameter, for every order: Lean convention; same instances. the law `discountMeasure` of the independent uniforms `U_{i,B}`: the discounts are functions of `U`; the coins do not enter these events. -/
theorem claim_4_6 {n m : ℕ} (hm : 1 ≤ m) (ord : LinearOrder (Alloc n m)) {ϵ : ℝ} (h0 : 0 < ϵ)
    (h1 : ϵ < 1) (v w : Profile n m) (hv : IsProfile v) (hw : IsProfile w) :
    emd ((randomDiscount ord ϵ).law (discountSeedMeasure n m) v)
        ((randomDiscount ord ϵ).law (discountSeedMeasure n m) w) ≤
      2 * (m : ℝ) * (discountMeasure n m).real
        {U | selected ord (discount ϵ U) v ≠ selected ord (discount ϵ U) w} := by sorry

end LipStableCA
