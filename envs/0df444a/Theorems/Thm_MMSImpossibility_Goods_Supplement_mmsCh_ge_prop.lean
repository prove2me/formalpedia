-- Prove2me | Theorems.Thm_MMSImpossibility_Goods_Supplement_mmsCh_ge_prop
-- name    : MMSImpossibility.Goods.Supplement.mmsCh_ge_prop
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:02:56.603576+00:00
-- url     : https://prove2.me/theorems/132024e6-b93b-4a87-8c20-72e928eb4e83
-- title:
--   §1.1 — chores maximin share at least the proportional share, $\mathrm{MMS}^{\mathrm{ch}}_i \ge \mathrm{PROP}^{\mathrm{ch}}_i$
-- statement:
--   Let $n \ge 1$ agents have nonnegative additive cost functions $c_1,\dots,c_n$ on a finite set $M$ of chores. Then for every agent $i$
--
--   $$\mathrm{MMS}^{\mathrm{ch}}_i \;\ge\; \mathrm{PROP}^{\mathrm{ch}}_i = \frac{c_i(M)}{n},$$
--
--   where $\mathrm{MMS}^{\mathrm{ch}}_i = \min_{(B_1,\dots,B_n)}\max_t c_i(B_t)$.
--
--   This average-cost lower bound is what turns an explicit partition into equal-cost bundles into the exact value of the chores maximin share, as in the proofs of Theorems 3 and 4.
--
--   **Formalization Note** $n \ge 1$ holds because an agent $i \in [n]$ is given.
--
--   Differences from the source:
--   - encoding: allocations as ordered partitions (B_1,…,B_n) of M; every item allocated → maps A : Fin m → Fin n with bundle A i = A⁻¹(i), and MMS^ch as ⨅ over such maps of ⨆ over Fin n; reason: maps and ordered partitions into possibly empty bundles coincide
--   - encoding: nonnegative additive cost functions c_i : 2^M → ℝ≥0 → a real-valued profile c : Fin n → Finset (Fin m) → ℝ with IsAdditive (additivity over singletons and c i S ≥ 0); reason: the same cost functions, nonnegativity stated as a property
-- source:
--   Ezra and Garbuz, Improved Impossibility Bounds for Maximin Share Allocations, 2026 preprint, STOC 2027 submission #115, SHA-256 8e8d63bbe3b0c850c561528c6e8d5bdb6da3bc426e5f64316cc948d5a31d64a6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/115.pdf, §1.1 Model (Chores), PDF p. 4 (printed p. 3)

import Mathlib
import Definitions.Def_MMSImpossibility_Goods_Supplement_Setting

namespace MMSImpossibility.Goods.Supplement

open LittleCharity.MMS MMSImpossibility.Goods

/-- §1.1 (PDF p. 4): for nonnegative additive costs, every agent's chores maximin share is at
least her proportional share, `MMS^ch_i ≥ PROP^ch_i = c_i(M)/n`. -/
theorem mmsCh_ge_prop {n m : ℕ} (c : Fin n → Finset (Fin m) → ℝ) (hc : IsAdditive c)
    (i : Fin n) :
    c i Finset.univ / n ≤ mmsCh (c i) n := by sorry

end MMSImpossibility.Goods.Supplement
