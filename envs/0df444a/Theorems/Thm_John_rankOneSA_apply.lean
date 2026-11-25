-- Prove2me | Theorems.Thm_John_rankOneSA_apply
-- name    : John.rankOneSA_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:35:15.685528+00:00
-- url     : https://prove2.me/theorems/0a88f582-af9d-42f9-9e71-d0b2d3113a88
-- title:
--   John: rank One SA apply
-- statement:
--   The John construction uses the rank One SA apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/John.lean#L272-L273
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/John.lean#L272-L273

module
public import Definitions.Def_BasicResults_Determinant
public import Definitions.Def_BasicResults_CompactConvexHull
public import Definitions.Def_BasicResults_JohnIngredients
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Seminorm
public import Mathlib.Topology.Order.Compact
public import Definitions.Def_BasicResults_John
set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped InnerProductSpace ComplexConjugate
open RCLike (re)
open John
variable {𝕜 : Type u} [RCLike 𝕜] {k : ℕ}

theorem John.rankOneSA_apply (u x : EuclideanSpace 𝕜 (Fin k)) :
    rankOneSA u x = ⟪u, x⟫_𝕜 • u := by sorry

attribute [defeq] John.rankOneSA_apply
