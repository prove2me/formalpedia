-- Prove2me | Theorems.Thm_HopfAlgebra_exists_finiteFlat_padicInt_of_ratLocalizedAt
-- name    : HopfAlgebra.exists_finiteFlat_padicInt_of_ratLocalizedAt
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:07:07.873948+00:00
-- url     : https://prove2.me/theorems/b35e7319-8859-4251-9774-33bb2595878e
-- title:
--   A finite flat cocommutative Hopf model yields a finite-flat p-adic representation
-- statement:
--   Let $p$ be prime and let $N$ be an abelian group with a global Galois action. Let $H_0$ be a finite flat cocommutative Hopf algebra over $ℚ$ localized at $p$. Assume an equivalence from the convolution group of algebra maps $H_0→\overline{ℚ}$ to $N$ that turns convolution into addition and is compatible with Galois transport. Then $$σ↦\operatorname{act}(\operatorname{locToGlob}_p(σ))\text{ is a finite-flat representation at }p.$$ This converts a Hopf-algebra model into the local finite-flat property used in Kummer theory.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_GroupCohomology_FiniteFlatCocycle

set_option autoImplicit false
open scoped TensorProduct Coalgebra.TensorProduct PadicInt
open HopfAlgebra

theorem HopfAlgebra.exists_finiteFlat_padicInt_of_ratLocalizedAt
    (p : ℕ) [Fact p.Prime]
    {N : Type} [AddCommGroup N]
    (act : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → N → N)
    (H0 : Type) [CommRing H0] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H0]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H0]
    [Module.Flat (GaloisRep.ratLocalizedAt p) H0]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H0]
    (e0 : WithConv (H0 →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ N)
    (he0_add : ∀ f g, e0 (f * g) = e0 f + e0 g)
    (he0_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H0 →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ h : H0, g h = σ (f h)) → e0 g = act σ (e0 f)) :
    groupCohomology.IsFiniteFlatRepresentation p
      (fun σ => act (localGaloisToGlobal p σ)) := by sorry
