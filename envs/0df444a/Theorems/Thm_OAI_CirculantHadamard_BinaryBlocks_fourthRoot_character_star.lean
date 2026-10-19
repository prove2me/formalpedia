-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_BinaryBlocks_fourthRoot_character_star
-- name    : OAI.CirculantHadamard.BinaryBlocks.fourthRoot_character_star
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:33:14.24497+00:00
-- url     : https://prove2.me/theorems/9bd5c171-4cec-472d-9416-9e8e2a838896
-- title:
--   The character of a fourth root of unity under conjugation
-- statement:
--   Let $S$ be a commutative star ring and $i\in S$ with $i^2=-1$ and $\bar i=-i$. Then for every $a\in\mathbb Z/4$, with exponents read in $\{0,1,2,3\}$,
--   $$
--   i^{-a}=\overline{i^{a}} .
--   $$
--
--   This is the hypothesis needed for partial evaluation at $i$ to commute with the involutions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/BinaryBlocks.lean#L255-L270

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
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryBlocks

open OAI OAI.CirculantHadamard OAI.CirculantHadamard.BinaryBlocks
universe uR uS
open CyclicRing
open scoped BigOperators
variable {R : Type uR} {S : Type uS} [CommRing R] [StarRing R] [CommRing S] [StarRing S]
variable (m : ℕ) [NeZero m]

theorem OAI.CirculantHadamard.BinaryBlocks.fourthRoot_character_star (i : S) (hi : i ^ 2 = -1) (hstar : star i = -i) :
    ∀ a : ZMod 4, i ^ (-a).val = star (i ^ a.val) := by sorry
