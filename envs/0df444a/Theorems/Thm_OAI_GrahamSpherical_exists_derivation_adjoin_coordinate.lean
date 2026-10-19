-- Prove2me | Theorems.Thm_OAI_GrahamSpherical_exists_derivation_adjoin_coordinate
-- name    : OAI.GrahamSpherical.exists_derivation_adjoin_coordinate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:12:40.143319+00:00
-- url     : https://prove2.me/theorems/e234b9be-80e5-45c1-b32d-be155e2c4d0d
-- title:
--   A unit derivation at one coordinate of an algebraically independent family
-- statement:
--   Let $(b_j)_{j\in\iota}$ be real numbers that are algebraically independent over $\mathbb{Q}$, and let $F=\mathbb{Q}(b_j:j\in\iota)\subseteq\mathbb{R}$. For every $i\in\iota$ there is a derivation $\delta$ of $F$ over $\mathbb{Z}$ with
--   $$
--   \delta(b_i)=1 .
--   $$
--
--   It is the partial derivative $\partial/\partial X_i$ transported to $F$ through the isomorphism $\mathbb{Q}(X_\iota)\cong F$ given by algebraic independence.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SphericalRamsey/BasisDerivation.lean#L90-L112

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.FieldTheory.Differential.Basic
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Definitions.Def_GrahamSpherical
import Definitions.Def_OAI_Combinatorics_SphericalRamsey_Model
import Definitions.Def_OAI_Combinatorics_SphericalRamsey_MonochromaticObstruction
import Definitions.Def_OAI_Combinatorics_SphericalRamsey_BasisDerivation

open OAI OAI.GrahamSpherical

theorem OAI.GrahamSpherical.exists_derivation_adjoin_coordinate {ι : Type*} (b : ι → ℝ)
    (hb : AlgebraicIndependent ℚ b) (i : ι) :
    ∃ D : Derivation ℤ (IntermediateField.adjoin ℚ (Set.range b))
      (IntermediateField.adjoin ℚ (Set.range b)),
      D ⟨b i, IntermediateField.subset_adjoin ℚ (Set.range b) ⟨i, rfl⟩⟩ = 1 := by sorry
