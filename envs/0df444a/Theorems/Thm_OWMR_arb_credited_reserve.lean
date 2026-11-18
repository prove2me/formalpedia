-- Prove2me | Theorems.Thm_OWMR_arb_credited_reserve
-- name    : OWMR.arb_credited_reserve
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-16T12:51:34.583398+00:00
-- url     : https://prove2.me/theorems/6f13fa27-8d35-45ba-a5e3-e18967205eda
-- title:
--   Lemma C.3: shipping at offset thresholds, crossing count, and the averaged reserve over the offset
-- statement:
--   Fix a request size $Q>0$ and a nondecreasing cumulative allocation path $A_0\le A_1\le\cdots$ with $0\le A_0$ and $A_k\le Q$. For an offset $\vartheta$, the request ships its whole allocation in period $k$ when the allocation rises to or past a threshold ($3Q\vartheta/4$, and $3Q(1+\vartheta)/4$ if $\vartheta<1/3$) or reaches $Q$; $S_k(\vartheta)$ (`shippedPath`) is the quantity shipped by period $k$. Let $N(\vartheta)=2$ if $\vartheta<1/3$ and $N(\vartheta)=1$ otherwise. Then:
--   1. $0\le S_k(\vartheta)\le A_k$, and $S_k(\vartheta)=Q$ when $A_k=Q$;
--   2. for $\vartheta>0$ and every $T$, the number of periods $k<T$ with a threshold crossing is at most $1+N(\vartheta)$;
--   3. for $z\ge0$ and $A_k<Q$, $\displaystyle\int_0^1\bigl(A_k-S_k(\vartheta)-z\bigr)^+d\vartheta\le\frac{\bigl((3Q/4-z)^+\bigr)^2}{3Q/2}$;
--   4. $\displaystyle\int_0^1\bigl(1+N(\vartheta)\bigr)d\vartheta=\frac73$.
--
--   Item 3 is the averaged retained reserve against the depletion $z$; item 4 gives the expected number of dispatches $7/3$.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Appendix C, Step 3, Lemma C.3 with (C.12)-(C.15), pp. E.12-E.14; dispatch thresholds of Definition 2, p. 27.

import Definitions.Def_owmr_consolidation_policy

open MeasureTheory
open scoped ENNReal

namespace OWMR
theorem arb_credited_reserve (Q : ℝ) (A : ℕ → ℝ) (hQ : 0 < Q) (hA0 : 0 ≤ A 0) (hA : Monotone A)
    (hAQ : ∀ k, A k ≤ Q) :
    (∀ θ k, 0 ≤ shippedPath Q θ A k ∧ shippedPath Q θ A k ≤ A k) ∧
    (∀ θ k, A k = Q → shippedPath Q θ A k = Q) ∧
    (∀ θ T, 0 < θ →
      ∑ k ∈ Finset.range T,
          (if crossesThreshold Q θ (if k = 0 then 0 else A (k - 1)) (A k) then (1 : ℝ) else 0)
        ≤ 1 + if θ < 1 / 3 then 2 else 1) ∧
    (∀ k z, 0 ≤ z → A k < Q →
      ∫⁻ θ in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (A k - shippedPath Q θ A k - z)
        ≤ ENNReal.ofReal (max (3 * Q / 4 - z) 0 ^ 2 / (3 * Q / 2))) ∧
    ∫⁻ θ in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (1 + if θ < 1 / 3 then 2 else 1)
      = ENNReal.ofReal (7 / 3) := by sorry
end OWMR
