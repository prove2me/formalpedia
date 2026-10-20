-- Prove2me | Theorems.Thm_OAI_SingleFold_CurveRank_representatives_card
-- name    : OAI.SingleFold.CurveRank.representatives_card
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:58:49.783228+00:00
-- url     : https://prove2.me/theorems/34ea164d-6c8e-4e90-9f9e-6b037b1df9cb
-- title:
--   At most eight representatives of $E(\mathbb{Q})/2E(\mathbb{Q})$
-- statement:
--   Let $E$ be $y^2=x^3-25x$, $T_0=(0,0)$, $T_5=(5,0)$ and $G=(25/4,75/8)$. The set of representatives
--   $$
--   \{O,T_0,T_5,T_0+T_5\}\ \cup\ \{O,T_0,T_5,T_0+T_5\}+G
--   $$
--   has at most $8$ elements.
--
--   Since these points cover $E(\mathbb{Q})$ modulo $2E(\mathbb{Q})$, the quotient has order at most $8$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/FiniteGeneration.lean#L78-L90

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

open OAI OAI.SingleFold OAI.SingleFold.CurveRank
open Descent

theorem OAI.SingleFold.CurveRank.representatives_card : representatives.card ≤ 8 := by sorry
