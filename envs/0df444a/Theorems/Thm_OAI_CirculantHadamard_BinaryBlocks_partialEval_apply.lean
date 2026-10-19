-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_BinaryBlocks_partialEval_apply
-- name    : OAI.CirculantHadamard.BinaryBlocks.partialEval_apply
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:31:28.365984+00:00
-- url     : https://prove2.me/theorems/634d49db-20aa-4e79-aede-33432bd91817
-- title:
--   Coefficients of partial evaluation at a fourth root
-- statement:
--   Let $\varphi:R\to S$ be a homomorphism of commutative rings, $z\in S$ with $z^4=1$, and $m>0$. For $f\in R[\mathbb Z/4\times\mathbb Z/m]$, its partial evaluation in $S[\mathbb Z/m]$ has coefficient at $b\in\mathbb Z/m$
--   $$
--   \sum_{j\in\mathbb Z/4}\varphi\bigl(f(j,b)\bigr)\,z^{j}.
--   $$
--
--   The $\mathbb Z/4$ coordinate is evaluated at $z$ while the $\mathbb Z/m$ coordinate is kept, so each coefficient combines the four blocks with weights $1,z,z^2,z^3$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/BinaryBlocks.lean#L129-L150

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
variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] (m : ℕ)
variable [NeZero m]

theorem OAI.CirculantHadamard.BinaryBlocks.partialEval_apply (φ : R →+* S) (z : S) (hz : z ^ 4 = 1)
    (f : ProductElem R m) (b : ZMod m) :
    (partialEval m φ z hz f).coeff b =
      ∑ j : ZMod 4, φ (f.coeff (j, b)) * z ^ j.val := by sorry
