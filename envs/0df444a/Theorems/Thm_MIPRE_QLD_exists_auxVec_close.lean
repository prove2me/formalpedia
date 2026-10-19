-- Prove2me | Theorems.Thm_MIPRE_QLD_exists_auxVec_close
-- name    : MIPRE.QLD.exists_auxVec_close
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:46:47.10538+00:00
-- url     : https://prove2.me/theorems/1f26e2b2-c5fa-472c-82f5-fc0eb26903cc
-- title:
--   The state estimate of lem:qld-swap, item 1. A unit state that is nearly invariant under both Weyl twirls on its two ancilla halves is close to a product aux (x) EPR
-- statement:
--   A statement of the module `MIPRE.Background.QLD.SwapState` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The swap isometry's state estimate (`lem:qld-swap`, item 1). `MIPRE/Background/QLD/SwapUnitary.lean` proves the two halves of item 1 separately: the algebra (`swapU_conj_wTilde_X`, `swapU_conj_wTilde_Z`: conjugation by the swap map carries the exact Pauli observables to bare generalized Paulis, with no error at all), the identity the estimate rests on (`twirl_mul_twirl`: the product of the two Weyl twirls is the maximally entangled projector), and the arithmetic that turns two near-invariances into a closeness (`norm_sub_sq_le_of_re_inner_ge`, `re_inner_ge_of_two_close`,…
--
--   **The state estimate of `lem:qld-swap`, item 1.**
--
--   A unit state that is nearly invariant under both Weyl twirls on its two ancilla halves is close to
--   a product `aux (x) EPR`. The two hypotheses are what the self-consistency of the exact Pauli
--   observables supplies after conjugation by the swap map (`swapU_conj_wTilde_X`,
--   `swapU_conj_wTilde_Z` carry `W~^e(u-tilde)` to `1 (x) tau^W(e u-tilde)` with no error), and they
--   are hypotheses here rather than conclusions: that self-consistency, at a *uniform* `u-tilde`, is
--   the paper's second item of `lem:qld-construct-the-paulis` and is what remains of stage 5.
--
--   The estimate itself is the appendix's, in the repaired form: `2 - 2 sqrt(1 - eta)` with
--   `eta = 2 sqrt(delta) + 2 delta`, which is `O(sqrt(delta))`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.QLD
--   open Finset Matrix MIPRE MIPRE.Weyl
--   open scoped Kronecker ComplexOrder MatrixOrder
--   variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
--   variable {n : Type*} [Fintype n] [DecidableEq n]
--   variable {R : Type*} [Fintype R] [DecidableEq R]
--
--   theorem MIPRE.QLD.exists_auxVec_close (θ : R × ((n → F) × (n → F)) → ℂ) (hθ : star θ ⬝ᵥ θ = 1)
--       {δ : ℝ} (hδ : 0 ≤ δ) (hlt : 2 * Real.sqrt δ + 2 * δ < 1)
--       (hX : 1 - δ / 2
--         ≤ (star θ ⬝ᵥ ((bOp (twirl (wX (F := F) (n := n))) :
--             Matrix (R × ((n → F) × (n → F))) (R × ((n → F) × (n → F))) ℂ) *ᵥ θ)).re)
--       (hZ : 1 - δ / 2
--         ≤ (star θ ⬝ᵥ ((bOp (twirl (wZ (F := F) (n := n))) :
--             Matrix (R × ((n → F) × (n → F))) (R × ((n → F) × (n → F))) ℂ) *ᵥ θ)).re) :
--       ∃ aux : R → ℂ, ‖evec (auxVec (F := F) (n := n) aux)‖ = 1 ∧
--         ‖evec θ - evec (auxVec (F := F) (n := n) aux)‖ ^ 2
--           ≤ 2 - 2 * Real.sqrt (1 - (2 * Real.sqrt δ + 2 * δ))
--   ```
--
--   **Formalization Note** `MIPRE.QLD.exists_auxVec_close` is declared in `MIPRE/Background/QLD/SwapState.lean`, lines 192–277. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/QLD/SwapState.lean#L192-L277; blueprint lem:qld-swap

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Background_QLD_ExactPauli
import Definitions.Def_MIPRE_Background_QLD_SwapUnitary
import Definitions.Def_MIPRE_Background_QLD_SwapState

open MIPRE
open MIPRE.QLD
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [Fintype R] [DecidableEq R]

theorem MIPRE.QLD.exists_auxVec_close (θ : R × ((n → F) × (n → F)) → ℂ) (hθ : star θ ⬝ᵥ θ = 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (hlt : 2 * Real.sqrt δ + 2 * δ < 1)
    (hX : 1 - δ / 2
      ≤ (star θ ⬝ᵥ ((bOp (twirl (wX (F := F) (n := n))) :
          Matrix (R × ((n → F) × (n → F))) (R × ((n → F) × (n → F))) ℂ) *ᵥ θ)).re)
    (hZ : 1 - δ / 2
      ≤ (star θ ⬝ᵥ ((bOp (twirl (wZ (F := F) (n := n))) :
          Matrix (R × ((n → F) × (n → F))) (R × ((n → F) × (n → F))) ℂ) *ᵥ θ)).re) :
    ∃ aux : R → ℂ, ‖evec (auxVec (F := F) (n := n) aux)‖ = 1 ∧
      ‖evec θ - evec (auxVec (F := F) (n := n) aux)‖ ^ 2
        ≤ 2 - 2 * Real.sqrt (1 - (2 * Real.sqrt δ + 2 * δ)) := by sorry
