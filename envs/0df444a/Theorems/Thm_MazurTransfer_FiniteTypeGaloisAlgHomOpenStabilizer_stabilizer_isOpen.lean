-- Prove2me | Theorems.Thm_MazurTransfer_FiniteTypeGaloisAlgHomOpenStabilizer_stabilizer_isOpen
-- name    : MazurTransfer.FiniteTypeGaloisAlgHomOpenStabilizer.stabilizer_isOpen
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T23:15:18.028511+00:00
-- url     : https://prove2.me/theorems/c6a99635-e505-4dc1-8816-555b732206d6
-- title:
--   A point of a finite-type algebra over an algebraic extension has an open automorphism stabilizer
-- statement:
--   Let K/F be an algebraic field extension, A a commutative F-algebra of finite type, and f an F-algebra homomorphism from A to K. For the canonical Krull topology on the automorphism group, $$\{\sigma\in\operatorname{Aut}_F(K):\sigma\circ f=f\}\ \text{is open}.$$ No Galois hypothesis is added. The named downstream consumers are finite-scheme geometric point stabilizers and continuous cocycles on actual norm fibres.
-- source:
--   Complete original MazurTheorem FiniteTypeGaloisAlgHomOpenStabilizer.stabilizer_isOpen statement and finite-generator proof, Apache-2.0. Preserves the original field, integral-extension and finite-type algebra hypotheses and canonical Mathlib Krull topology. Complete original final type is compared independently. Named consumer: FiniteSchemeGeometricPointOpenStabilizer.stabilizer_isOpen and continuous actual norm Kummer cocycles.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a field-valued point of a finite type algebra has an
open Galois stabilizer for the Krull topology of an algebraic extension.
Named downstream consumer: geometric points on the finite actual norm
fibres and continuous Kummer cocycles.
-/
import Mathlib
noncomputable section

theorem MazurTransfer.FiniteTypeGaloisAlgHomOpenStabilizer.stabilizer_isOpen (F K A : Type) [Field F] [Field K] [Algebra F K]
    [Algebra.IsIntegral F K] [CommRing A] [Algebra F A] [Algebra.FiniteType F A] (f : A →ₐ[F] K) :
    IsOpen {σ : K ≃ₐ[F] K | σ.toAlgHom.comp f = f} := by sorry
