-- Prove2me | Theorems.Thm_OAI_SingleFold_EllipticModel_W_index
-- name    : OAI.SingleFold.EllipticModel.W_index
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:10:52.217331+00:00
-- url     : https://prove2.me/theorems/8d874ee9-2315-41fb-a17c-0229e3afbcf8
-- title:
--   Heights of even multiples depend only on the index
-- statement:
--   Let $E:y^2=x^3-25x$ and fix an isomorphism $E(\mathbb{Q})\cong\mathbb{Z}\times T$ with $T$ finite and generator $P$ of the free part. For $Q$ with index $i(Q)\in\mathbb{Z}$, let $W_m(Q)=H(mQ)$ be the height of the $x$-coordinate of $mQ$, and $s_m(j)=W_m(jP)$. If $m$ is even, then
--   $$
--   W_m(Q)=s_m\bigl(|i(Q)|\bigr) .
--   $$
--
--   Multiplying by an even $m$ removes the torsion part, and the height is symmetric under $Q\mapsto-Q$. So $W_m$ is a function of $|i(Q)|$ alone.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/EllipticGrowth.lean#L85-L96

import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticGrowth

open OAI OAI.SingleFold OAI.SingleFold.EllipticModel
open WeierstrassCurve.Affine.Point
variable {T : Type} [AddCommGroup T]
variable (f : E.Point ≃+ (Fin 1 → ℤ)×T)

theorem OAI.SingleFold.EllipticModel.W_index [Finite T] (m : ℕ) (hm : Even m) (Q : E.Point) : W m Q=sequence f m (index f Q).natAbs := by sorry
