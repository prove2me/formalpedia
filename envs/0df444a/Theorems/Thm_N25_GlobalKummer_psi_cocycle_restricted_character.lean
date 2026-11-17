-- Prove2me | Theorems.Thm_N25_GlobalKummer_psi_cocycle_restricted_character
-- name    : N25.GlobalKummer.psi_cocycle_restricted_character
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:53:53.635953+00:00
-- url     : https://prove2.me/theorems/4f36a712-319b-40f2-b461-423c6a64ce14
-- title:
--   A $ψ$-cocycle restricts to a finite character over the quintic field
-- statement:
--   Let $F=ℚ(ζ_{25})^{H_{25}}$ be the quintic character field, let $c\in Z^1(G_{ℚ},𝔽_{71}(ψ))$, and assume that $c$ factors through a finite quotient. Then there is an embedding $j:F\hookrightarrow ℚ̄$ for which $ℚ̄/j(F)$ is Galois, every $j(F)$-automorphism has $ψ=1$, and every $σ\in G_{ℚ}$ with $ψ(σ)=1$ fixes $j(F)$. Moreover the restriction of $c$ is a multiplicative character $f$ on $G_F$, it factors through a finite extension $E/F$, and the class number of $F$ is at most $7$: $$f(τ)=c(τ|_{G_{ℚ}}),\qquad [E:F]<\infty,\qquad G_E\subseteq\ker f,\qquad h_F\le7.$$ This packages the restricted character and the arithmetic bound that force its vanishing. Formalization note: the algebra and scalar-tower instances are the canonical structures induced by the chosen embedding $j$.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_GlobalKummerSequence
import Definitions.Def_N25_CharacterField
import Definitions.Def_N25_LocalKummerCharacter
import Definitions.Def_N25
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Invariant.Basic

set_option autoImplicit false
noncomputable section
open N25
open N25.GlobalKummer
local instance psiRestrictedPrimeSeventyOne_i9cc59a : Fact (Nat.Prime 71) := ⟨by decide⟩

theorem N25.GlobalKummer.psi_cocycle_restricted_character
    (c : groupCohomology.cocycles₁ psiRep)
    (hc : groupCohomology.IsLevelConstant₁ (MonoidHom.id Gal) c) :
    ∃ j : characterField →ₐ[ℚ] AlgebraicClosure ℚ,
      letI : Algebra characterField (AlgebraicClosure ℚ) := j.toRingHom.toAlgebra
      letI : IsScalarTower ℚ characterField (AlgebraicClosure ℚ) := IsScalarTower.of_algHom j
      IsGalois characterField (AlgebraicClosure ℚ) ∧
      (∀ τ : AlgebraicClosure ℚ ≃ₐ[characterField] AlgebraicClosure ℚ,
        psi (τ.restrictScalars ℚ) = 1) ∧
      (∀ σ : Gal, psi σ = 1 → ∀ x : characterField, σ (j x) = j x) ∧
      ∃ f : (AlgebraicClosure ℚ ≃ₐ[characterField] AlgebraicClosure ℚ) →*
          Multiplicative (ZMod 71),
        (∀ σ, f σ = Multiplicative.ofAdd (c (σ.restrictScalars ℚ))) ∧
        (∃ E : IntermediateField characterField (AlgebraicClosure ℚ),
          FiniteDimensional characterField E ∧ E.fixingSubgroup ≤ f.ker) ∧
        NumberField.classNumber characterField ≤ 7 := by sorry
