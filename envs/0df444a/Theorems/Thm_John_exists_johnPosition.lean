-- Prove2me | Theorems.Thm_John_exists_johnPosition
-- name    : John.exists_johnPosition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:43:21.806105+00:00
-- url     : https://prove2.me/theorems/0332ebd8-f383-45c1-9aea-cef902a8afa6
-- title:
--   John: exists john Position
-- statement:
--   **John position along an equivalence.** Given a continuous linear equivalence
--   `L : 𝕜^k ≃L W` onto a normed space `W` (with `0 < k`), there are an equivalence
--   `M : 𝕜^k ≃L W` and a body seminorm `q` in *John position*: `q` is continuous, the
--   identity is feasible for `q` (`q u ≤ ‖u‖`), every feasible operator has `‖det‖ ≤ 1`,
--   and `q` is the pullback of the norm of `W` along `M` (`‖M z‖ = q z`).
--
--   Mathematically: pull the norm of `W` back to a body seminorm `p = ‖L ·‖` on `𝕜^k`
--   (equivalent to the Euclidean norm since `L` is an equivalence and `k > 0`), take a
--   maximal-volume feasible operator `T₀` (`exists_maxVolume`), and set `q = p ∘ T₀`,
--   `M = L ∘ T₀`. This is the common core of the Kadets–Snobar and Garling–Gordon
--   projection theorems below.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/John.lean#L168-L238
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/John.lean#L168-L238

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

theorem John.exists_johnPosition {W : Type u} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    (hk : 0 < k) (L : EuclideanSpace 𝕜 (Fin k) ≃L[𝕜] W) :
    ∃ (M : EuclideanSpace 𝕜 (Fin k) ≃L[𝕜] W)
      (q : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k))),
      Continuous q ∧ (∀ u, q u ≤ ‖u‖) ∧ (∀ S ∈ Feasible q, ‖S.det‖ ≤ 1) ∧
      ∀ z, ‖M z‖ = q z := by sorry
