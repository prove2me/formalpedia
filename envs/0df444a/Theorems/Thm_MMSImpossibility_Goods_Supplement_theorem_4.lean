-- Prove2me | Theorems.Thm_MMSImpossibility_Goods_Supplement_theorem_4
-- name    : MMSImpossibility.Goods.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:04:09.757615+00:00
-- url     : https://prove2.me/theorems/c9ff4a3f-e92f-412a-848a-6b585e8461af
-- title:
--   Theorem 4 — $\beta^{\mathrm{MMS}} \ge 31/30$, witnessed by four agents and eleven chores
-- statement:
--   There is an additive chores instance with four agents and eleven chores in which:
--
--   1. every agent has $\mathrm{MMS}^{\mathrm{ch}}_i = \mathrm{PROP}^{\mathrm{ch}}_i = c_i(M)/4 = 90$;
--   2. $\min_{(B_1,\dots,B_4)} \max_i c_i(B_i) = 93$: every allocation gives some agent cost at least $93$, and some allocation gives every agent cost at most $93$.
--
--   Consequently
--
--   $$\beta_4^{\mathrm{MMS}} \ge \frac{93}{90} = \frac{31}{30} \qquad\text{and}\qquad \beta^{\mathrm{MMS}} = \sup_{n\ge1}\beta_n^{\mathrm{MMS}} \ge \frac{31}{30}.$$
--
--   No MMS approximation factor strictly smaller than $31/30$ can therefore be guaranteed for all additive chores instances.
--
--   **Formalization Note** $\beta_4^{\mathrm{MMS}}$ is `betaMMS 4` and $\beta^{\mathrm{MMS}}$ is `betaMMSAll`, both in `EReal`.
--
--   Differences from the source:
--   - generalization: β^MMS ≥ 31/30 → additionally: an additive instance on Fin 4 agents and Fin 11 chores with MMS^ch_i = c_i(M)/4 = 90 for every agent, every allocation giving some agent cost ≥ 93 and some allocation giving every agent cost ≤ 93, and β_4^MMS ≥ 31/30; reason: these are what the proof establishes (§5, PDF p. 14: 'MMSch_i = PROPch_i = 360/4 = 90', 'min … max ci(Bi) = 93', 'β^MMS ≥ β_4^MMS ≥ 31/30'); the conjunction contains the theorem verbatim
--   - encoding: allocations as ordered partitions (B_1,…,B_n) of M; every item allocated → maps A : Fin 11 → Fin 4 with bundle A i = A⁻¹(i); reason: maps and ordered partitions into possibly empty bundles coincide
--   - encoding: nonnegative additive cost functions c_i : 2^M → ℝ≥0 → real-valued c i : Finset (Fin 11) → ℝ with IsAdditive (additivity over singletons and c i S ≥ 0); reason: the same cost functions, nonnegativity stated as a property
--   - encoding: β_n^MMS = sup over instances and β^MMS = sup_{n≥1} β_n^MMS (real suprema, no finiteness asserted) → betaMMS n and betaMMSAll as suprema in EReal of the real ratios; reason: the paper asserts no boundedness; EReal gives the same supremum when it is finite and +∞ otherwise, so the lower bound means exactly what the page says
-- source:
--   Ezra and Garbuz, Improved Impossibility Bounds for Maximin Share Allocations, 2026 preprint, STOC 2027 submission #115, SHA-256 8e8d63bbe3b0c850c561528c6e8d5bdb6da3bc426e5f64316cc948d5a31d64a6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/115.pdf, Theorem 4, PDF p. 6 (printed p. 5); instance and proof §5, PDF p. 14 (printed p. 13); Appendix B.2, PDF p. 18

import Mathlib
import Definitions.Def_MMSImpossibility_Goods_Supplement_Setting

namespace MMSImpossibility.Goods.Supplement

open LittleCharity.MMS MMSImpossibility.Goods

/-- Theorem 4 (PDF p. 6), with what its proof (§5, PDF p. 14; Appendix B.2) establishes:
1. there is an additive chores instance with four agents and eleven chores in which every agent
   has `MMS^ch_i = PROP^ch_i = 90`, and `min_B max_i c_i(B_i) = 93`: every allocation gives
   some agent cost at least `93`, and some allocation gives every agent cost at most `93`;
2. `β_4^MMS ≥ 31/30`;
3. `β^MMS ≥ 31/30`. -/
theorem theorem_4 :
    (∃ c : Fin 4 → Finset (Fin 11) → ℝ,
      IsAdditive c ∧
      (∀ i, mmsCh (c i) 4 = 90 ∧ c i Finset.univ / 4 = 90) ∧
      (∀ A : Fin 11 → Fin 4, ∃ i, 93 ≤ c i (bundle A i)) ∧
      ∃ A : Fin 11 → Fin 4, ∀ i, c i (bundle A i) ≤ 93) ∧
    ((31 / 30 : ℝ) : EReal) ≤ betaMMS 4 ∧
    ((31 / 30 : ℝ) : EReal) ≤ betaMMSAll := by sorry

end MMSImpossibility.Goods.Supplement
