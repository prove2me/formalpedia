-- Prove2me | Theorems.Thm_MMSImpossibility_Goods_Supplement_theorem_2
-- name    : MMSImpossibility.Goods.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:02:25.750468+00:00
-- url     : https://prove2.me/theorems/6843799c-824f-4152-834f-bfbfcdee536e
-- title:
--   Theorem 2 — $\alpha^{\mathrm{MMS}} \le 20/21$, witnessed by four agents and eleven goods
-- statement:
--   There is an additive goods instance with four agents and eleven goods in which:
--
--   1. every agent has $\mathrm{MMS}_i = \mathrm{PROP}_i = v_i(M)/4 = 21$;
--   2. every allocation $(B_1,\dots,B_4)$ of the eleven goods gives some agent $i$ value $v_i(B_i) \le 20$.
--
--   Consequently
--
--   $$\alpha_4^{\mathrm{MMS}} \le \frac{20}{21} \qquad\text{and}\qquad \alpha^{\mathrm{MMS}} = \inf_{n\ge1}\alpha_n^{\mathrm{MMS}} \le \frac{20}{21}.$$
--
--   This improves the constant upper bound $39/40$ of Feige, Sapir and Tauber on the MMS approximation ratio that can be guaranteed for all additive goods instances.
--
--   **Formalization Note** $\mathrm{MMS}_i$ is the published `LittleCharity.MMS.mms`, $\alpha_n^{\mathrm{MMS}}$ the published `alphaMMS`, and $\alpha^{\mathrm{MMS}}$ is `alphaMMSAll`.
--
--   Differences from the source:
--   - generalization: α^MMS ≤ 20/21 → additionally: an additive instance on Fin 4 agents and Fin 11 goods with MMS_i = v_i(M)/4 = 21 for every agent in which every allocation gives some agent value ≤ 20, and α_4^MMS ≤ 20/21; reason: these are what the proof establishes (§3, PDF p. 12: 'every agent has MMS equal to 21, but every allocation gives some agent value at most 20 ... this establishes α4MMS ≤ 20/21'); the conjunction contains the theorem verbatim
--   - encoding: allocations as ordered partitions (B_1,…,B_n) of M; every item allocated → maps A : Fin 11 → Fin 4 with bundle A i = A⁻¹(i); reason: maps and ordered partitions into possibly empty bundles coincide
--   - encoding: nonnegative additive valuations v_i : 2^M → ℝ≥0 → real-valued v i : Finset (Fin 11) → ℝ with IsAdditive (additivity over singletons and v i S ≥ 0); reason: the same valuations, nonnegativity stated as a property
--   - encoding: α^MMS = inf_{n≥1} α_n^MMS → sInf {r : ℝ | ∃ n, 1 ≤ n ∧ r = alphaMMS n}; reason: the set is nonempty and bounded below by 0, so the real sInf is the infimum
-- source:
--   Ezra and Garbuz, Improved Impossibility Bounds for Maximin Share Allocations, 2026 preprint, STOC 2027 submission #115, SHA-256 8e8d63bbe3b0c850c561528c6e8d5bdb6da3bc426e5f64316cc948d5a31d64a6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/115.pdf, Theorem 2, PDF p. 6 (printed p. 5); instance and proof §3, PDF pp. 12–13 (printed pp. 11–12); Appendix B.1, PDF pp. 17–18

import Mathlib
import Definitions.Def_MMSImpossibility_Goods_Supplement_Setting

namespace MMSImpossibility.Goods.Supplement

open LittleCharity.MMS MMSImpossibility.Goods

/-- Theorem 2 (PDF p. 6), with what its proof (§3, PDF pp. 12–13; Appendix B.1) establishes:
1. there is an additive goods instance with four agents and eleven goods in which every agent
   has `MMS_i = PROP_i = 21`, and every allocation of the eleven goods gives some agent value
   at most `20`;
2. `α_4^MMS ≤ 20/21`;
3. `α^MMS ≤ 20/21`. -/
theorem theorem_2 :
    (∃ v : Fin 4 → Finset (Fin 11) → ℝ,
      IsAdditive v ∧
      (∀ i, mms (v i) 4 Finset.univ = 21 ∧ v i Finset.univ / 4 = 21) ∧
      ∀ A : Fin 11 → Fin 4, ∃ i, v i (bundle A i) ≤ 20) ∧
    alphaMMS 4 ≤ 20 / 21 ∧
    alphaMMSAll ≤ 20 / 21 := by sorry

end MMSImpossibility.Goods.Supplement
