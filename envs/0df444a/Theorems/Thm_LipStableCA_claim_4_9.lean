-- Prove2me | Theorems.Thm_LipStableCA_claim_4_9
-- name    : LipStableCA.claim_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:52:35.150983+00:00
-- url     : https://prove2.me/theorems/7c8022d4-d122-4f8d-9c85-725f577f0a19
-- title:
--   Claim 4.9 — a multiplicative window for a discount
-- statement:
--   Let $h$ be a bidder, let $B$ be a nonempty bundle, let $b\in\mathbb R$, and let $\eta\ge 0$. Then the discount $a_{h,B}$ of Mechanism 2 satisfies
--   $$\Pr\bigl[b\le a_{h,B}\le e^\eta b\bigr]\le\frac m\epsilon\,\eta\,\Pr\bigl[a_{h,B}>b\bigr]^{1-1/m}.$$
--
--   The factor $\Pr[a_{h,B}>b]^{1-1/m}$ is what lets Hölder's inequality reduce the sum over $2^m$ bundles to a factor $R^{1/m}$ in Lemma 4.8.
--
--   **Formalization Note.** At $m=1$ the exponent is $0$ and $0^0=1$, which is what the paper's estimate needs.
--
--   Differences from the source:
--   - encoding: $m,n\ge 1$ throughout (§5 says so; Mechanism 2 has $U^{1/m}$) → the hypothesis `1 ≤ m`; reason: the paper's standing setting; excludes only the empty item set
--   - encoding: Pr over the seed of Mechanism 2 → the law `discountMeasure` of the independent uniforms $U_{i,B}$; reason: the discounts are functions of $U$; the coins do not enter these events
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Claim 4.9, p.16

import Definitions.Def_LipStableCA_randomDiscount

namespace LipStableCA

/-- **Claim 4.9.** Afshinmehr, Koutsoupias, *Lipschitz Stable Combinatorial Auctions*, STOC 2027 submission (manuscript sha256 c5e4c53f…), p.16. **Formalization Note.** the hypothesis `1 ≤ m`: the paper's standing setting; excludes only the empty item set. the law `discountMeasure` of the independent uniforms `U_{i,B}`: the discounts are functions of `U`; the coins do not enter these events. -/
theorem claim_4_9 {n m : ℕ} (hm : 1 ≤ m) {ϵ : ℝ} (h0 : 0 < ϵ) (h1 : ϵ < 1) (h : Fin n)
    (B : Finset (Fin m)) (hB : B ≠ ∅) (b η : ℝ) (hη : 0 ≤ η) :
    (discountMeasure n m).real {U | b ≤ discount ϵ U h B ∧ discount ϵ U h B ≤ Real.exp η * b} ≤
      (m : ℝ) / ϵ * η * ((discountMeasure n m).real {U | b < discount ϵ U h B}) ^ (1 - 1 / (m : ℝ)) := by sorry

end LipStableCA
