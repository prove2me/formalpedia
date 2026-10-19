-- Prove2me | Theorems.Thm_MazurTransfer_FiniteRationalFibreGaloisOrbit_stabilizer_isOpen
-- name    : MazurTransfer.FiniteRationalFibreGaloisOrbit.stabilizer_isOpen
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T23:27:28.929262+00:00
-- url     : https://prove2.me/theorems/e40b36d1-be39-404c-886b-504769f65696
-- title:
--   A point in a finite rational fibre has open Galois stabilizer
-- statement:
--   Let F be a field and K an algebraic extension of F. Let X and Y be F-schemes and phi:X to Y a finite F-morphism. If a is an F-valued point of Y and b a K-valued point of X above a, then $$\operatorname{Stab}_{\operatorname{Aut}_F(K)}(b)$$ is open in the Krull topology. The literal pullback fibre is used, with the original spectrum-map action. This supplies continuity of actual norm preimage orbits and kernel cocycles.
-- source:
--   Original MazurTheorem FiniteRationalFibreGaloisOrbit.stabilizer_isOpen and its original pointAction constructor. Apache-2.0; complete original target type, helper type and helper value compared.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a field-valued preimage of a rational point under a
finite morphism has an open Galois stabilizer. The literal pullback
fibre is used. Named downstream consumer: actual norm kernels and
continuous preimage cocycles.
-/
import Theorems.Thm_MazurTransfer_FiniteSchemeGeometricPointOpenStabilizer_stabilizer_isOpen
import Definitions.Def_MazurTransfer_FieldPointActionsAndNormPreimageDifferenceData
import Definitions.Def_MazurTransfer_GaloisFixedOverPointScalarExtensionData

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MazurTransfer.FieldAutomorphismOverPointAction MazurTransfer.GaloisFixedOverPointDescent

theorem MazurTransfer.FiniteRationalFibreGaloisOrbit.stabilizer_isOpen (F K : Type) [Field F] [Field K] [Algebra F K] [Algebra.IsIntegral F K]
    {X Y : Scheme.{0}} (tX : X ⟶ Spec (CommRingCat.of F)) (tY : Y ⟶ Spec (CommRingCat.of F)) (φ : Over.mk tX ⟶ Over.mk tY) [IsFinite φ.left]
    (a : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ Over.mk tY)
    (b : Over.mk (fieldBase F K) ⟶ Over.mk tX) (hb : b ≫ φ = scalarOverMap F K ≫ a) :
    IsOpen {σ : K ≃ₐ[F] K | fieldAut F K σ ≫ b = b} := by sorry
