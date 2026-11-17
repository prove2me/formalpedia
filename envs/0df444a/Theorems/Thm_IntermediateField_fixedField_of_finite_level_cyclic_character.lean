-- Prove2me | Theorems.Thm_IntermediateField_fixedField_of_finite_level_cyclic_character
-- name    : IntermediateField.fixedField_of_finite_level_cyclic_character
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:04:57.55579+00:00
-- url     : https://prove2.me/theorems/914a5316-5e2b-4afc-b9be-0a5edbe1bc16
-- title:
--   A surjective finite-level cyclic character cuts out a finite cyclic Galois extension
-- statement:
--   Let $L/K$ be Galois, let $G$ be a finite cyclic group, and let $f:\operatorname{Gal}(L/K)→G$ be surjective. Assume there is a finite-dimensional intermediate field $E/K$ whose fixing subgroup is contained in $\ker f$. Then the fixed field $M=L^{\ker f}$ is finite-dimensional and Galois over $K$, its automorphism group over $K$ is cyclic, and $$[M:K]=|G|.$$ This identifies the finite extension cut out by a continuous cyclic character.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

set_option autoImplicit false
open IntermediateField

theorem IntermediateField.fixedField_of_finite_level_cyclic_character
    {K L G : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [Group G] [Finite G] [IsCyclic G]
    (f : (L ≃ₐ[K] L) →* G) (hf : Function.Surjective f)
    (hlevel : ∃ E : IntermediateField K L,
      FiniteDimensional K E ∧ E.fixingSubgroup ≤ f.ker) :
    FiniteDimensional K (fixedField f.ker) ∧
      IsGalois K (fixedField f.ker) ∧
      IsCyclic ((fixedField f.ker) ≃ₐ[K] (fixedField f.ker)) ∧
      Module.finrank K (fixedField f.ker) = Nat.card G := by sorry
