-- Prove2me | Theorems.Thm_NSWBetter_theorem_3_14
-- name    : NSWBetter.theorem_3_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:56:24.133327+00:00
-- url     : https://prove2.me/theorems/e2aff44b-b750-4e4b-8863-3fdb949e47ec
-- title:
--   Theorem 3.14 — replacing the large goods, removing and adding small goods
-- statement:
--   Let $I$ be a well-behaved instance with $\Delta\ge1$ identical agents and nonnegative values satisfying Assumption 3.5, with large goods $L$, $\ell=|L|$, and mean value $\mu$. Form $I^{mod}$ by
--   1. replacing $L$ by new goods $L'$, each of value $>\Delta\mu/(\Delta-\ell)$, with $|L'|\in[100\gamma\Delta,\Delta]$;
--   2. removing a set $R$ of small goods with $v(R)\le|L'|\mu/100$;
--   3. adding goods $A$, each of value in $[0,\Delta\mu/(\Delta-\ell)]$, with $v(A)\le\Delta\mu$.
--
--   Then
--   $$\mathrm{logNSW}(W^{mod})\ge\frac1\Delta\Bigl[\sum_{g\in L'}\ln v(g)+(\Delta-|L'|)\ln\mu\Bigr]+\frac{(\Delta-|L'|)v(A)}{10\Delta^2\mu}-\frac{3(\Delta-|L'|)v(R)}{\Delta^2\mu}-15\gamma .$$
--
--   Differences from the source:
--   - encoding: identical valuation with $\Delta$ agents → `v : Fin m → ℝ`, $v\ge0$, $\Delta\ge1$; reason: Lean convention; same instances
--   - encoding: $\mathrm{logNSW}(W^{mod})$ with $\ln0=-\infty$ → `EReal` via `HayashiHoeffding.elog`; reason: same values whenever finite
--   - encoding: the new goods $L'$, $A$ and the modified instance → multisets of values, $I^{mod}$ as a value multiset; reason: round robin depends only on the values; same instances
--   - encoding: goods of $A$ have values in $\mathbb R_{\ge0}$ → $0\le a$ for $a\in A$; reason: valuations are nonnegative (p.8); same instances
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Theorem 3.14, p.15

import Mathlib
import Definitions.Def_NSWBetter_gamma
import Definitions.Def_NSWBetter_largeCount
import Definitions.Def_NSWBetter_meanVal
import Definitions.Def_NSWBetter_vals
import Definitions.Def_NSWBetter_largeGoods
import Definitions.Def_NSWBetter_Asm35
import Definitions.Def_NSWBetter_logNSWrr
import Definitions.Def_NSWBetter_WellBehaved

namespace NSWBetter

/-- **Theorem 3.14.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Theorem 3.14, p.15: "Let I be a well-behaved instance that satisfies Assumption 3.5 with ∆ identical agents, a set of large goods L and mean value µ. Let Imod be the instance that results from making the following modifications to I: 1. Replace the set of large goods L with a new set of large goods L′ such that v(g) > ∆µ/(∆−ℓ) for each new large good g ∈ L′, and |L′| ∈ [100γ∆, ∆]. 2. Remove a set R of small goods from I such that v(R) ≤ |L′|µ/100. 3. Add a set A of small goods to I such that v(g) ≤ ∆µ/(∆−ℓ) for each g ∈ A, and v(A) ≤ ∆µ. Define Wmod to be the round robin allocation in the instance Imod. The following holds: logNSW(Wmod) ≥ (1/∆)[Σ_(g∈L′) ln v(g) + (∆−|L′|) ln µ] + (∆−|L′|)v(A)/(10∆²µ) − 3(∆−|L′|)v(R)/(∆²µ) − 15γ."

**Formalization Note.** `Imod` has value multiset `L′ + {v(g) : g small, g ∉ R} + A`. -/
theorem theorem_3_14 (Δ m : ℕ) (hΔ : 1 ≤ Δ) (v : Fin m → ℝ) (hv : ∀ g, 0 ≤ v g)
    (h35 : Asm35 Δ (vals v)) (hwb : WellBehaved Δ (vals v)) (L' A : Multiset ℝ)
    (hL' : ∀ a ∈ L', (Δ : ℝ) * meanVal Δ (vals v) / ((Δ : ℝ) - largeCount Δ (vals v)) < a)
    (hL'card : 100 * gamma * Δ ≤ (L'.card : ℝ) ∧ L'.card ≤ Δ)
    (R : Finset (Fin m)) (hR : ∀ g ∈ R, g ∉ largeGoods Δ v)
    (hRval : ∑ g ∈ R, v g ≤ (L'.card : ℝ) * meanVal Δ (vals v) / 100)
    (hA : ∀ a ∈ A, 0 ≤ a ∧ a ≤ (Δ : ℝ) * meanVal Δ (vals v) / ((Δ : ℝ) - largeCount Δ (vals v)))
    (hAsum : A.sum ≤ (Δ : ℝ) * meanVal Δ (vals v)) :
    (((1 / Δ : ℝ) * ((L'.map Real.log).sum + ((Δ : ℝ) - L'.card) * Real.log (meanVal Δ (vals v))) +
        ((Δ : ℝ) - L'.card) * A.sum / (10 * (Δ : ℝ) ^ 2 * meanVal Δ (vals v)) -
        3 * ((Δ : ℝ) - L'.card) * (∑ g ∈ R, v g) / ((Δ : ℝ) ^ 2 * meanVal Δ (vals v)) -
        15 * gamma : ℝ) : EReal) ≤
      logNSWrr Δ (L' + ((Finset.univ \ largeGoods Δ v) \ R).val.map v + A) := by sorry

end NSWBetter
