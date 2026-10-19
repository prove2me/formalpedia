-- Prove2me | Theorems.Thm_MIPRE_sum_condFail_le_of_pushforward
-- name    : MIPRE.sum_condFail_le_of_pushforward
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:08:51.463022+00:00
-- url     : https://prove2.me/theorems/7ee236e6-5b61-45a2-bf5d-9aff885ede35
-- title:
--   The blueprint's "divided by the probability that the subtest is selected", in the form the Pauli basis test needs. An auxiliary weighting ν on an index set and a map q to…
-- statement:
--   A statement of the module `MIPRE.Foundations.CrossConsistency` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Cross-party consistency, and what winning a subtest buys. The Pauli appendix's `≃_δ` compares `A ⊗ Id` with `Id ⊗ B`: one player's operator against the *other* player's. `MIPRE.stateDist` of `def:state-distance` compares two families on the same side, which is what the orthonormalization step needs; this file is the cross-party form, and the one lemma that produces it.
--
--   **The blueprint's "divided by the probability that the subtest is selected", in the form the
--   Pauli basis test needs.** An auxiliary weighting `ν` on an index set and a map `q` to question
--   pairs whose *pushforward* stays below `μ / c` gives `∑_i ν i · condFail (q i) ≤ ε / c`. Unlike
--   `sum_condFail_le_of_le` this asks nothing of `q`: the subtests of the Pauli basis test are
--   indexed by the verifier's content, and several contents give the same question pair whenever the
--   types involved do not read all of it --- a `(Pauli, W)` question reads none of it at all.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix Kronecker
--   open scoped ComplexOrder MatrixOrder
--   variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
--   variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
--   variable {ε : ℝ}
--
--   theorem MIPRE.sum_condFail_le_of_pushforward {ι : Type*} [Fintype ι] [DecidableEq ι]
--       [DecidableEq X] [DecidableEq Y]
--       (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue G ψ MA MB ≤ ε) (ν : ι → ℝ)
--       (q : ι → X × Y) {c : ℝ} (hc : 0 < c)
--       (hpush : ∀ p : X × Y, c * ∑ i ∈ univ.filter fun i => q i = p, ν i ≤ G.μ p.1 p.2) :
--       ∑ i, ν i * condFail G ψ MA MB (q i).1 (q i).2 ≤ ε / c
--   ```
--
--   **Formalization Note** `MIPRE.sum_condFail_le_of_pushforward` is declared in `MIPRE/Foundations/CrossConsistency.lean`, lines 389–420. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CrossConsistency.lean#L389-L420; blueprint def:cross-distance

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B

open MIPRE
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
variable {ε : ℝ}

theorem MIPRE.sum_condFail_le_of_pushforward {ι : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq X] [DecidableEq Y]
    (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue G ψ MA MB ≤ ε) (ν : ι → ℝ)
    (q : ι → X × Y) {c : ℝ} (hc : 0 < c)
    (hpush : ∀ p : X × Y, c * ∑ i ∈ univ.filter fun i => q i = p, ν i ≤ G.μ p.1 p.2) :
    ∑ i, ν i * condFail G ψ MA MB (q i).1 (q i).2 ≤ ε / c := by sorry
