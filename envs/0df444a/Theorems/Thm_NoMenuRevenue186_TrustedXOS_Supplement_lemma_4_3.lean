-- Prove2me | Theorems.Thm_NoMenuRevenue186_TrustedXOS_Supplement_lemma_4_3
-- name    : NoMenuRevenue186.TrustedXOS.Supplement.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:04:59.756205+00:00
-- url     : https://prove2.me/theorems/500157a4-bcd1-4d45-91de-55298984241c
-- title:
--   Lemma 4.3 — buy-many extension of the Lemma 4.2 menu
-- statement:
--   Consider the almost-disjoint construction of Section 4.1 (the published `Construction`, satisfying its validity conditions) with overlap parameter $\epsilon$ and maximum scale $V=2^K$, and assume
--
--   $$\epsilon V<1-\epsilon.$$
--
--   Then there are prices $p_D$ on bundles and a purchase rule, both depending only on the seller's prior $D$, such that for every seller prior $D=D_{A,u}$ of the construction:
--
--   1. $p_D$ is nonnegative, normalized ($p_D(\emptyset)=0$), monotone and subadditive, and the purchase rule picks, for every valuation in the support of $D$, an option (a bundle or no trade) maximizing $v(T)-p_D(T)$;
--   2. at every supported instantiation $(D_{A,u},v_{B,u_{S^*}})$ with $A\cap B=\{S^*\}$ the chosen purchase pays exactly $(1-\epsilon)u_{S^*}$ and is a bundle $T$ with value $v_{B,u_{S^*}}(T)=u_{S^*}$.
--
--   This shows that the buy-many benchmark $\mathrm{Opt}_{bm}$ of the construction is at least $(1-\epsilon)\mathbb E[u_{S^*}]$, which is what the buy-many lower bound (Theorem 3.3) needs.
--
--   Differences from the source:
--   - encoding: supported instantiations (D_{A,u}, v_{B,u_{S*}}) and welfare u_{S*} of the allocation → seeds a in C.seeds and collections with C.Supported a B S; the chosen option is some T with C.value B (a.2 S) T = 2^(a.2 S); reason: the same parameterization of the joint support as the published Lemma 4.2; welfare is the buyer value of the allocated bundle
--   - generalization: the construction of Section 4.1 built from a family supplied by Lemma 4.1 → any construction satisfying Construction.Valid; reason: as for the published Lemma 4.2, the proof uses the family only through separation and the size and divisibility conditions; every source construction is valid
-- source:
--   Aggarwal, Dang, Rubinstein, Zhao, STOC 2027 submission #186 (October 2026), printed p.16, PDF p.18, Lemma 4.3; proof Appendix A.1, printed p.36, PDF p.38

import Mathlib
import Definitions.Def_NoMenuRevenue186_TrustedXOS_Construction

namespace NoMenuRevenue186.TrustedXOS.Supplement
open NoMenuRevenue186.TrustedXOS

/-- Lemma 4.3, printed p.16 (PDF p.18), proof in Appendix A.1 (printed p.36). The prices and
    the choice rule are functions of the actual seller prior only (seller-prior-contingent).
    Prices are nonnegative and subadditive (`BuyManyPrices`), normalized and monotone; at every
    supported instantiation the chosen purchase pays `(1 - ε) u_{S*}` and has welfare `u_{S*}`. -/
theorem lemma_4_3 {n : ℕ} (C : Construction n) (hC : C.Valid)
    (hεV : C.ε * (C.V : ℝ) < 1 - C.ε) :
    ∃ (price : Prior n → Bundle n → ℝ)
      (choice : Prior n → Valuation n → Option (Bundle n)),
      ∀ a ∈ C.seeds,
        BuyManyFeasible (C.prior a) (price (C.prior a)) (choice (C.prior a)) ∧
        price (C.prior a) ∅ = 0 ∧ Monotone (price (C.prior a)) ∧
        ∀ (B : Finset (Bundle n)) (S : Bundle n), C.Supported a B S →
          menuPayment (price (C.prior a)) (choice (C.prior a) (C.value B (a.2 S))) =
              (1 - C.ε) * (2 : ℝ) ^ (a.2 S).val ∧
          ∃ T : Bundle n, choice (C.prior a) (C.value B (a.2 S)) = some T ∧
            C.value B (a.2 S) T = (2 : ℝ) ^ (a.2 S).val := by sorry

end NoMenuRevenue186.TrustedXOS.Supplement
