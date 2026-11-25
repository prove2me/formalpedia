-- Prove2me | Theorems.Thm_John_exists_gap_of_lt_one_on_compact
-- name    : John.exists_gap_of_lt_one_on_compact
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:23:05.255165+00:00
-- url     : https://prove2.me/theorems/9436d657-0f5d-439b-ac93-48a55cf9cdef
-- title:
--   John: exists gap of lt one on compact
-- statement:
--   **Uniform gap on a compact set.** If a continuous seminorm satisfies `q < 1` on a
--   compact set `C`, it stays below `1 - η` on `C` for a uniform `0 < η ≤ 1` (extreme value
--   theorem; `η ≤ 1` because `q ≥ 0`).
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/John.lean#L518-L528
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/John.lean#L518-L528

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

theorem John.exists_gap_of_lt_one_on_compact {q : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k))}
    (hqc : Continuous q) {C : Set (EuclideanSpace 𝕜 (Fin k))} (hC : IsCompact C)
    (hlt : ∀ u ∈ C, q u < 1) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ u ∈ C, q u ≤ 1 - η := by sorry
