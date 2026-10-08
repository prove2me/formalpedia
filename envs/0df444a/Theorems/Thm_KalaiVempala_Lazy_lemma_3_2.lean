-- Prove2me | Theorems.Thm_KalaiVempala_Lazy_lemma_3_2
-- name    : KalaiVempala.Lazy.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:46:03.633153+00:00
-- url     : https://prove2.me/theorems/3c0e67e0-f5de-4dd3-9e62-83c4b8c7b9f0
-- title:
--   Lemma 3.2, p. 300 — the cubes [0,1/ε]ⁿ and v+[0,1/ε]ⁿ overlap in at least a (1 − ε|v|₁) fraction
-- statement:
--   **Overlap of shifted cubes.** Let $\varepsilon > 0$ and let $U$ be the uniform probability measure on the cube $[0, 1/\varepsilon]^n$. For every $v \in \mathbb R^n$,
--
--   $$U\big(\{x : x - v \in [0, 1/\varepsilon]^n\}\big) \;\ge\; 1 - \varepsilon |v|_1, \qquad |v|_1 = \sum_{i=1}^n |v_i| .$$
--
--   That is, the cubes $[0, 1/\varepsilon]^n$ and $v + [0, 1/\varepsilon]^n$ overlap in at least a $(1 - \varepsilon|v|_1)$ fraction of their volume. In this mission it gives the update bound of FLL.
--
--   **Formalization Note** The fraction is the $U$-measure of the overlap, written in `ℝ≥0∞`; when $1 - \varepsilon|v|_1 < 0$ the left side is $0$ and the claim is trivial, as on the page. $U$ is `perturbLaw n ε` from `OracleRO.ApproxFPL.FPL`. The statement is identical to Lemma 3.2 of the companion mission on FPL($\varepsilon$), restated because draft items cannot import each other.
-- source:
--   Kalai & Vempala, Efficient algorithms for online decision problems, J. Comput. System Sci. 71 (2005), p. 300, Lemma 3.2 (proof p. 301)

import Mathlib
import Definitions.Def_OracleRO_ApproxFPL_FPL
import Definitions.Def_KalaiVempala_Lazy_Setting

open MeasureTheory OracleRO.ApproxFPL

namespace KalaiVempala.Lazy

theorem lemma_3_2 {n : ℕ} (ε : ℝ) (hε : 0 < ε) (v : Fin n → ℝ) :
    ENNReal.ofReal (1 - ε * ∑ i, |v i|) ≤
      perturbLaw n ε {x | x - v ∈ Set.Icc (0 : Fin n → ℝ) (fun _ => ε⁻¹)} := by sorry

end KalaiVempala.Lazy
