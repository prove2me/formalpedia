-- Prove2me | Theorems.Thm_NumberField_LevelArith_exists_placesAbove_inr_equiv_primesOver
-- name    : NumberField.LevelArith.exists_placesAbove_inr_equiv_primesOver
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/ffa847e6-de75-5a24-a9f5-ab167aaa471e
-- title:
--   Primes above q as Γ_L-orbits on Γ/D_q
-- statement:
--   Let $K\subseteq L$ be intermediate fields of $\overline{\mathbb Q}/\mathbb Q$ (inside `AlgebraicClosure ℚ`), both of finite degree over $\mathbb Q$, write $\Gamma=\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ and let `levelField K L hKL` be $L$ regarded as an extension of $K$; assume $L/K$ is normal (as a typeclass hypothesis) and assume the project's condition `IsNormalLevel K L`, i.e. $\gamma s\gamma^{-1}$ fixes $L$ pointwise whenever $\gamma$ fixes $K$ pointwise and $s$ fixes $L$ pointwise. Let $S$ be a finite set of rational primes and $q\in S$. The theorem asserts the existence of a bijection $e$ between `placesAbove L S (Sum.inr q)`, the set of orbits of the fixing subgroup of $L$ acting on the coset space $\Gamma/D_q$, where $D_q$ is the image in $\Gamma$ of the local Galois group at $q$ under `extArithLoc S (Sum.inr q)`, and the set of height-one primes $w$ of $\mathcal O_{L}$ (the ring of integers of `levelField K L hKL`) whose ideal contains the image of the natural number $q$, such that $e$ is equivariant for the fixing subgroup of $K$ in the following ideal-theoretic form: for every $\gamma$ fixing $K$ pointwise and every orbit $x$, the ideal of $e(\gamma\cdot x)$, the action on orbits being `orbitQuotientAction`, equals the image of the ideal of $e(x)$ under the automorphism of $\mathcal O_{L}$ induced by `levelGal K L hKL γ`, the restriction of $\gamma$ to a $K$-algebra automorphism of `levelField K L hKL`.
--
--   This is the classical identification of the primes of a number field $L$ above a rational prime $q$ with the orbits of $\mathrm{Gal}(\overline{\mathbb Q}/L)$ on $\Gamma/D_q$, packaged as a bijection equivariant for the relative Galois action of $L/K$ and phrased through the transport of ideals. It serves the counting of places in the $H^2$ computations over $S$-integers, and is used by the statements on the cyclotomic $H^2$ representation and on the bound for the torsion of continuous $H^2$ of the Galois $S$-unit representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_exists_placesAbove_inr_equiv_primesOver.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module Limits groupCohomology ExtCitation NumberField.LevelArith IsDedekindDomain
open scoped Classical NumberField NumberField.LevelArith TensorProduct Pointwise

theorem NumberField.LevelArith.exists_placesAbove_inr_equiv_primesOver
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L]
    (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)] (hnorm : IsNormalLevel K L) (S : Finset Nat.Primes) (q : ↥S) :
    ∃ e : placesAbove L S (Sum.inr q) ≃
        {w : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥(levelField K L hKL)) // ((((q : Nat.Primes) : ℕ) : 𝓞 ↥(levelField K L hKL)) ∈ w.asIdeal)},
      ∀ (γ : ↥K.fixingSubgroup) (x : placesAbove L S (Sum.inr q)),
        ((e ((orbitQuotientAction K L hnorm ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (extArithLoc S (Sum.inr q)).range)).smul γ x)).1).asIdeal =
          ((e x).1).asIdeal.map (ringOfIntegersAut ↥K ↥(levelField K L hKL) (levelGal K L hKL γ)) := by sorry
