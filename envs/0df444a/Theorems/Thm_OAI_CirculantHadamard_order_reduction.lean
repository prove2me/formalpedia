-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_order_reduction
-- name    : OAI.CirculantHadamard.order_reduction
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-19T09:30:38.253992+00:00
-- url     : https://prove2.me/theorems/da195d0f-b16c-4921-bed0-778d9ed2e65c
-- title:
--   The order of a circulant Hadamard matrix is four times an odd square
-- statement:
--   Let $n>1$ and suppose there is a real circulant $n\times n$ matrix $H$ with entries $\pm1$ and $HH^{\mathsf T}=nI$. Then
--   $$
--   n=4u^2
--   $$
--   for some odd $u>0$.
--
--   This is the classical restriction on circulant Hadamard orders, proved here by a two-adic descent in cyclic group rings.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/OrderReduction.lean#L20-L38

import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalDVR
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_IntegerTwoLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicPolynomial
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedConjugation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicIntegerEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_DyadicRemainder
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedEisenstein
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_OrderHalving

open OAI OAI.CirculantHadamard

theorem OAI.CirculantHadamard.order_reduction {n : ℕ} (hn : 1 < n)
    (h : ExistsRealCirculantHadamard n) :
    ∃ u : ℕ, 0 < u ∧ Odd u ∧ n = 4 * u ^ 2 := by sorry
