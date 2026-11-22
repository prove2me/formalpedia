-- Prove2me | Theorems.Thm_MatchingLogic_Applicative_coord_eq
-- name    : MatchingLogic.Applicative.coord_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:48.312248+00:00
-- url     : https://prove2.me/theorems/47e66ee9-41f4-40c9-a3ee-32cc7fd2bfc1
-- title:
--   Applicative: coord eq
-- statement:
--   **"It has two coordinates."**  A constant contributes none, and the binary
--   symbol contributes exactly two.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Applicative.lean#L69-L78
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Applicative.lean#L69-L78

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_MatchingLogic_Localization
public import Definitions.Def_LeanPool_MatchingLogic_Composite
public import Definitions.Def_LeanPool_MatchingLogic_Applicative
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open MatchingLogic.Applicative
variable {Const : Type} {Var : Type} [DecidableEq Var]

theorem MatchingLogic.Applicative.coord_eq (e : Coord (appSig Const)) : e = coord₁ ∨ e = coord₂ := by sorry
