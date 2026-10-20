-- Prove2me | Theorems.Thm_OAI_SingleFold_GrowthCompilation_graph_sf
-- name    : OAI.SingleFold.GrowthCompilation.graph_sf
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:11:35.397206+00:00
-- url     : https://prove2.me/theorems/d49267e2-008f-404a-b4d5-9fcdd905e556
-- title:
--   The growth function defined by height brackets is single-fold
-- statement:
--   Let $E:y^2=x^3-25x$ with an isomorphism $E(\mathbb{Q})\cong\mathbb{Z}\times T$, $T$ finite, and fix $m,\kappa\in\mathbb{N}$. Suppose that for every $u$ there is a unique growth pair $A=(Q,R)$: $Q$ and $R$ are torsion-normalized representatives, $Q$ brackets $u$, and $(Q,R)$ is a $\kappa$-window. Then the relation on $(u,v)\in\mathbb{N}^2$
--   $$
--   \exists A\ \bigl(A\text{ is a growth pair for }u\ \wedge\ v=W_m(A_2)\bigr)
--   $$
--   has a single-fold Diophantine representation.
--
--   This is the single-fold graph of a function $u\mapsto W_m(R_u)$ of controlled super-polynomial growth. It serves as the growth function of the exponentiation system.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/EllipticGrowth.lean#L440-L484

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

open OAI OAI.SingleFold OAI.SingleFold.GrowthCompilation
open Compiler PointCompiler
variable {T : Type} [AddCommGroup T] [Finite T]
variable (f : OAI.SingleFold.GrowthCompilation.E.Point ≃+ (Fin 1 → ℤ)×T)

theorem OAI.SingleFold.GrowthCompilation.graph_sf (m κ : ℕ) (hunique : ∀ u, ∃! A, EllipticModel.GrowthPair f m κ u A) :
    SF (fun z : Fin 2 → ℕ => ∃ A, EllipticModel.GrowthPair f m κ (z 0) A ∧ EllipticModel.W m A.2=z 1) := by sorry
