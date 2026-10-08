-- Prove2me | Theorems.Thm_OAI_AbhyankarSathaye_CommutingDerivations_commuting_derivations_with_ordinary_extras
-- name    : OAI.AbhyankarSathaye.CommutingDerivations.commuting_derivations_with_ordinary_extras
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:20.254238+00:00
-- url     : https://prove2.me/theorems/d995dd33-a729-456b-b6a9-d45e738bf592
-- statement:
--   The theorem states that for every integer n ≥ 4, let A = ℂ[X₀, …, Xₙ₋₁], put h = X₀, u = X₁, v = X₂, w = X₃, and define x = u³ + hv, y = −u² + hw, s = 2u³v + 3u⁴w + h(v² − 3u²w²) + h²w³, p = −2s²x + 3sy² − 3s³y, and F = h − p − 1. There exist n − 1 ℂ-linear derivations d₀, …, dₙ₋₂ of A with all the following properties. Each dᵢ annihilates F + 1; the derivations commute pairwise on every polynomial; and each is locally nilpotent, meaning that for every a ∈ A some nonnegative iterate of dᵢ sends a to zero. They are linearly independent over A. Their common kernel is exactly the ℂ-subalgebra ℂ[F]: a polynomial a is annihilated by every dᵢ if and only if a belongs to ℂ[F]. Moreover, for every polynomial g in this common kernel, there is no ℂ-algebra automorphism e of A and no index j with e(Xⱼ) = g. Finally, for each integer i with 0 ≤ i < n − 4, dᵢ₊₃ is the ordinary partial derivative with respect to Xᵢ₊₄.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CommutingDerivations.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CommutingDerivations.lean; bytes 1553..2330
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.RingTheory.Adjoin.Basic
import Definitions.Def_CommutingDerivations

namespace OAI

noncomputable section

namespace AbhyankarSathaye

namespace CommutingDerivations

variable {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B]

open MvPolynomial

theorem commuting_derivations_with_ordinary_extras (n : ℕ) (hn : 4 ≤ n) :
    ∃ d : Fin (n-1) → Derivation ℂ (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ),
      (∀ i, d i (extendedF hn + 1) = 0) ∧
      (∀ i j p, d i (d j p) = d j (d i p)) ∧
      (∀ i, LocallyNilpotent (d i)) ∧
      LinearIndependent (MvPolynomial (Fin n) ℂ) d ∧
      (∀ p, (∀ i, d i p = 0) ↔
        p ∈ Algebra.adjoin ℂ ({extendedF hn} : Set (MvPolynomial (Fin n) ℂ))) ∧
      (∀ g, (∀ i, d i g = 0) →
        ¬ ∃ (e : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ) (j : Fin n),
          e (X j) = g) ∧
      (∀ i : Fin (n-4), d (blocksToOutput hn (Sum.inl i)) =
        pderiv (blocksToAmbient hn (Sum.inl i))) := by
  sorry

end CommutingDerivations
end AbhyankarSathaye
end
end OAI
