-- Prove2me | Theorems.Thm_GlobalTheory_T_vanishing_ideal_cone_prime_homogeneous
-- name    : GlobalTheory.T.vanishing_ideal_cone_prime_homogeneous
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:01:49.965348+00:00
-- url     : https://prove2.me/theorems/7932abed-15d4-43e2-a51b-3fc4268707ef
-- title:
--   T: vanishing ideal cone prime homogeneous
-- statement:
--   The T construction uses the vanishing ideal cone prime homogeneous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/VanishingIdealConePrimeHomogeneousStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/VanishingIdealConePrimeHomogeneousStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_VanishingIdealConePrimeHomogeneous
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_VanishingIdealConePrimeHomogeneousStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem GlobalTheory.T.vanishing_ideal_cone_prime_homogeneous : (∀ (k : Type) [Field k] [IsAlgClosed k] (X : Scheme.{0}) (p : X ⟶ Sp k) (H : LB X) (J : Type) [Fintype J] (s : J → H.Sec) (J₀ : Set J), H.IsLB → ImmBy p H s J₀ → IsIntegral X → ∀ g : ℕ, SmoothOfRelativeDimension g p → (MvPolynomial.vanishingIdeal k (cone p H s)).IsPrime ∧ (MvPolynomial.vanishingIdeal k (cone p H s)).IsHomogeneous (MvPolynomial.homogeneousSubmodule J k) ∧ (∃ i, MvPolynomial.X i ∉ MvPolynomial.vanishingIdeal k (cone p H s)) ∧ ringKrullDim (MvPolynomial J k ⧸ MvPolynomial.vanishingIdeal k (cone p H s)) = (g + 1 : ℕ)) := by sorry
