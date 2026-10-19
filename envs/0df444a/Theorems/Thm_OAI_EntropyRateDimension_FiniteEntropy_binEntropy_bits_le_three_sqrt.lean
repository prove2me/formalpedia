-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_binEntropy_bits_le_three_sqrt
-- name    : OAI.EntropyRateDimension.FiniteEntropy.binEntropy_bits_le_three_sqrt
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:02:42.336075+00:00
-- url     : https://prove2.me/theorems/7c379449-63bc-4ef6-abc4-abfddfeeed16
-- title:
--   Binary entropy in bits is at most three square roots
-- statement:
--   For $0\le q\le1$, let $h(q)=-q\log q-(1-q)\log(1-q)$ be the binary entropy in natural units. Then
--   $$
--   \frac{h(q)}{\log2}\le3\sqrt q .
--   $$
--
--   So a flag of probability $q$ carries at most $3\sqrt q$ bits of information.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/FiniteEntropy.lean#L513-L528

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteEntropy
universe uι uα uβ uγ uδ
open scoped BigOperators ENNReal
open MeasureTheory

theorem OAI.EntropyRateDimension.FiniteEntropy.binEntropy_bits_le_three_sqrt {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    Real.binEntropy q / Real.log 2 ≤ 3 * Real.sqrt q := by sorry
