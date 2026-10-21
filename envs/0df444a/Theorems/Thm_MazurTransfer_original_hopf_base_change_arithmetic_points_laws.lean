-- Prove2me | Theorems.Thm_MazurTransfer_original_hopf_base_change_arithmetic_points_laws
-- name    : MazurTransfer.original_hopf_base_change_arithmetic_points_laws
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-21T01:47:37.96335+00:00
-- url     : https://prove2.me/theorems/fc517449-474b-48aa-8b02-710d239b0af2
-- statement:
--   The original arithmetic point restriction from the scalar base change of the same Hopf algebra is its original point equivalence. It evaluates by the original tensor inclusion, preserves convolution multiplication, and commutes with every original coefficient-algebra map. All original commutative rings, algebra structures and scalar-tower hypotheses are retained. Named downstream consumer: transport of the actual selected nineteen character quotient to the equivalent rational-subring base.

import Definitions.Def_MazurTransfer_OriginalHopfBaseChangeArithmeticPointsData20261020
noncomputable section
open scoped TensorProduct
open MazurTransfer.HopfBaseChangeArithmeticPoints

theorem MazurTransfer.original_hopf_base_change_arithmetic_points_laws : (∀ {R S H K : Type} [CommRing R] [CommRing S] [Algebra R S] [CommRing H] [HopfAlgebra R H] [CommRing K] [Algebra R K] [Algebra S K] [IsScalarTower R S K], ∀ (f : WithConv (S ⊗[R] H →ₐ[S] K)) (h : H),
restrictPoint f h = f (1 ⊗ₜ[R] h)) ∧ (∀ {R S H K : Type} [CommRing R] [CommRing S] [Algebra R S] [CommRing H] [HopfAlgebra R H] [CommRing K] [Algebra R K] [Algebra S K] [IsScalarTower R S K], ∀ (f g : WithConv (S ⊗[R] H →ₐ[S] K)),
restrictPoint (f * g) = restrictPoint f * restrictPoint g) ∧ (∀ {R S H K : Type} [CommRing R] [CommRing S] [Algebra R S] [CommRing H] [HopfAlgebra R H] [CommRing K] [Algebra R K] [Algebra S K] [IsScalarTower R S K], ∀ {K' : Type} [CommRing K'] [Algebra R K']
    [Algebra S K'] [IsScalarTower R S K'] (a : K →ₐ[S] K')
    (f : WithConv (S ⊗[R] H →ₐ[S] K)),
restrictPoint (.toConv (a.comp f.ofConv)) =
      WithConv.toConv ((a.restrictScalars R).comp (restrictPoint f).ofConv)) := by sorry
