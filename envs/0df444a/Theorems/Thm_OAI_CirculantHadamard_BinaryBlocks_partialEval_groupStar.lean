-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_BinaryBlocks_partialEval_groupStar
-- name    : OAI.CirculantHadamard.BinaryBlocks.partialEval_groupStar
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:32:35.704982+00:00
-- url     : https://prove2.me/theorems/702e95d4-30c6-4630-abc8-db215ba26bda
-- title:
--   Partial evaluation commutes with the involutions
-- statement:
--   Let $R,S$ be commutative star rings, $\varphi:R\to S$ a ring homomorphism with $\varphi(\bar r)=\overline{\varphi(r)}$, and $z\in S$ with $z^4=1$ and $z^{-a}=\overline{z^{a}}$ for all $a\in\mathbb Z/4$. Then for every $f\in R[\mathbb Z/4\times\mathbb Z/m]$,
--   $$
--   P(f^{*})=P(f)^{*},
--   $$
--   where $P$ is partial evaluation at $z$ and $f^{*}(g)=\overline{f(-g)}$ on both group rings.
--
--   So a norm identity $ff^{*}=c$ on the product group survives partial evaluation.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/BinaryBlocks.lean#L216-L236

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

theorem OAI.CirculantHadamard.BinaryBlocks.partialEval_groupStar (φ : R →+* S) (z : S) (hz : z ^ 4 = 1)
    (hφ : ∀ r, φ (star r) = star (φ r))
    (hchar : ∀ a : ZMod 4, z ^ (-a).val = star (z ^ a.val))
    (f : ProductElem R m) :
    partialEval m φ z hz (groupStar f) = ringStar (partialEval m φ z hz f) := by sorry
