-- Prove2me | Theorems.Thm_LipStableCA_observation_4_2
-- name    : LipStableCA.observation_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:51:00.576015+00:00
-- url     : https://prove2.me/theorems/9868e82d-053e-4d58-a0ec-05a3417b15a1
-- title:
--   Observation 4.2 — the expected payment is at most the discounted value
-- statement:
--   For every reported profile $v$ and every realization of the discounts, the quantity $\bar p_i=\max_{T\in\mathcal A}\sum_{h\ne i}a_{h,T_h}v_h(T_h)-\sum_{h\ne i}a_{h,S^*_h}v_h(S^*_h)$ of Mechanism 2 satisfies
--   $$0\le\bar p_i\le a_{i,S^*_i}\,v_i(S^*_i)$$
--   for every bidder $i$.
--
--   It makes the payment $\bar p_i/a_{i,S^*_i}$ of a delivered bundle nonnegative and at most the bundle's value.
--
--   Differences from the source:
--   - encoding: a total order on $\mathcal A$ fixed before the reports are seen → an explicit `LinearOrder` parameter, for every order; reason: Lean convention; same instances
--   - encoding: a realization of the discounts → a realization of $U\in[0,1]^{\cdots}$; reason: the discounts are functions of $U$; $U\in[0,1]$ is the support
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Observation 4.2, p.14

import Definitions.Def_LipStableCA_randomDiscount

namespace LipStableCA

/-- **Observation 4.2.** Afshinmehr, Koutsoupias, *Lipschitz Stable Combinatorial Auctions*, STOC 2027 submission (manuscript sha256 c5e4c53f…), p.14. **Formalization Note.** an explicit `LinearOrder` parameter, for every order: Lean convention; same instances. a realization of `U∈[0,1]^{…}`: the discounts are functions of `U`; `U∈[0,1]` is the support. -/
theorem observation_4_2 {n m : ℕ} (ord : LinearOrder (Alloc n m)) {ϵ : ℝ} (h0 : 0 < ϵ) (h1 : ϵ < 1)
    (U : Fin n → Finset (Fin m) → ℝ) (hU : ∀ h C, U h C ∈ Set.Icc (0 : ℝ) 1) (v : Profile n m)
    (hv : IsProfile v) (i : Fin n) :
    0 ≤ expectedPayment ord (discount ϵ U) v i ∧
      expectedPayment ord (discount ϵ U) v i ≤
        discount ϵ U i ((selected ord (discount ϵ U) v).1 i) *
          v i ((selected ord (discount ϵ U) v).1 i) := by sorry

end LipStableCA
