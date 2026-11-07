-- Prove2me | Theorems.Thm_NSWBetter_lemma_3_16
-- name    : NSWBetter.lemma_3_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:56:06.076901+00:00
-- url     : https://prove2.me/theorems/4274c746-0acb-441e-801c-47bbf3fa83bc
-- title:
--   Lemma 3.16 — allocations with at most one good per large class are sub-optimal
-- statement:
--   Let $I$ be a well-behaved instance with $\Delta\ge1$ identical agents and nonnegative values satisfying Assumption 3.5, with large goods $L$, $\ell=|L|$, and mean value $\mu$. Partition the small goods into classes $G_1,\dots,G_k$ of equal value with $|G_j|\le\Delta$. Let $Y$ be an allocation with positive Nash welfare in which every agent receives at most one good of each class. If
--   $$\sum_{j=1}^k\mathbb 1\{|G_j|>0.5\Delta\}\,v(G_j)\ge\gamma\Delta\mu,$$
--   then
--   $$\mathrm{logNSW}(Y)<\frac1\Delta\Bigl[\sum_{g\in L}\ln v(g)+(\Delta-\ell)\ln\frac{\Delta\mu}{\Delta-\ell}\Bigr]-\gamma^2 .$$
--
--   Differences from the source:
--   - encoding: identical valuation with $\Delta$ agents → `v : Fin m → ℝ`, $v\ge0$, $\Delta\ge1$; reason: Lean convention; same instances
--   - encoding: a partition of the small goods into classes → a labelling `cls : Fin m → ℕ` read on the small goods, with equal values on equal labels; reason: every such partition is a labelling; same instances
--   - encoding: allocation $Y$ with positive Nash welfare → `Y : Fin m → Option (Fin Δ)` with every utility $>0$; reason: a product of nonnegative utilities is positive iff each factor is; same allocations
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Lemma 3.16, p.15

import Mathlib
import Definitions.Def_NSWBetter_gamma
import Definitions.Def_NSWBetter_largeCount
import Definitions.Def_NSWBetter_meanVal
import Definitions.Def_NSWBetter_vals
import Definitions.Def_NSWBetter_largeGoods
import Definitions.Def_NSWBetter_Asm35
import Definitions.Def_NSWBetter_WellBehaved

namespace NSWBetter

/-- **Lemma 3.16 — sub-optimal allocations.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Lemma 3.16, p.15: "Let I be a well-behaved instance that satisfies Assumption 3.5 with ∆ identical agents, a set of large goods L and mean value µ. Assume the small goods are partitioned into classes G1, G2, . . . , Gk such that all goods in the same class have the same value and |Gj| ≤ ∆ for each j ∈ [k]. Let Y be an allocation in this instance with positive Nash welfare where all agents receive at most one good from each class. If Σ_(j=1)^k 1{|Gj| > 0.5∆} v(Gj) ≥ γ∆µ, then logNSW(Y) < (1/∆)[Σ_(g∈L) ln v(g) + (∆−ℓ) ln(∆µ/(∆−ℓ))] − γ²."

**Formalization Note.** Classes are a labelling `cls` of the small goods; `Y` is a `∆`-subpartition; positive Nash welfare means every agent's utility is positive, so all logarithms are of positive numbers. -/
theorem lemma_3_16 (Δ m : ℕ) (hΔ : 1 ≤ Δ) (v : Fin m → ℝ) (hv : ∀ g, 0 ≤ v g)
    (h35 : Asm35 Δ (vals v)) (hwb : WellBehaved Δ (vals v)) (cls : Fin m → ℕ)
    (hcls : ∀ g ∉ largeGoods Δ v, ∀ g' ∉ largeGoods Δ v, cls g = cls g' → v g = v g')
    (hsize : ∀ j : ℕ, ((Finset.univ \ largeGoods Δ v).filter fun g => cls g = j).card ≤ Δ)
    (Y : Fin m → Option (Fin Δ))
    (hYpos : ∀ i : Fin Δ, 0 < ∑ g ∈ Finset.univ.filter (fun g => Y g = some i), v g)
    (hYone : ∀ (i : Fin Δ) (j : ℕ),
      ((Finset.univ \ largeGoods Δ v).filter fun g => cls g = j ∧ Y g = some i).card ≤ 1)
    (hbig : gamma * Δ * meanVal Δ (vals v) ≤
      ∑ j ∈ (Finset.univ \ largeGoods Δ v).image cls,
        if (0.5 : ℝ) * Δ < (((Finset.univ \ largeGoods Δ v).filter fun g => cls g = j).card : ℝ)
        then ∑ g ∈ (Finset.univ \ largeGoods Δ v).filter (fun g => cls g = j), v g else 0) :
    (1 / Δ : ℝ) * ∑ i : Fin Δ, Real.log (∑ g ∈ Finset.univ.filter (fun g => Y g = some i), v g) <
      (1 / Δ : ℝ) * (∑ g ∈ largeGoods Δ v, Real.log (v g) +
        ((Δ : ℝ) - largeCount Δ (vals v)) *
          Real.log ((Δ : ℝ) * meanVal Δ (vals v) / ((Δ : ℝ) - largeCount Δ (vals v)))) -
        gamma ^ 2 := by sorry

end NSWBetter
