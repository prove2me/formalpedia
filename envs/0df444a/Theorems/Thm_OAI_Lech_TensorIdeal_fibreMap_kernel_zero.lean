-- Prove2me | Theorems.Thm_OAI_Lech_TensorIdeal_fibreMap_kernel_zero
-- name    : OAI.Lech.TensorIdeal.fibreMap_kernel_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:35:00.688014+00:00
-- url     : https://prove2.me/theorems/c95e23ea-fbf8-48ee-9c92-133e2f771f42
-- title:
--   OAI.Lech.TensorIdeal.fibreMap_kernel_zero: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech.TensorIdeal`, with `open CategoryTheory`, `open scoped TensorProduct`):
--
--   ```lean
--   lemma fibreMap_kernel_zero (ell : TorsionLength I) (hds : ell.DirectSumZero)
--       (hg : Function.Surjective g) (hTc : powerTorsion I (ModuleCat.of R C))
--       (hkg : ell.value (ModuleCat.of R g.ker)=0) :
--       ell.value (ModuleCat.of R (fibreMap I (A:=A) (B:=B) V).ker)=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.TorsionLength` and `OAI.Lech.powerTorsion` (definitions bundle `OAIQ032L000` of this split); `OAI.Lech.TensorIdeal.fibreMap` (definitions bundle `OAIQ032L016` of this split); `OAI.Lech.TorsionLength.DirectSumZero` (definitions bundle `OAIQ032L017` of this split).
--
--   **Used by.** The proof of `OAI.Lech.ReesRoot.fibreCech_homology` of this split imports it.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ032L016
import Definitions.Def_OAIQ032L017

section

attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.TensorIdeal
open CategoryTheory
open scoped TensorProduct
universe u

section Square
variable {R A B C D : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [CommRing B] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
  [AddCommGroup C] [Module A C] [Module R C] [IsScalarTower R A C]
  [AddCommGroup D] [Module A D] [Module R D] [IsScalarTower R A D]
  (I : Ideal R) (a : A →ₗ[A] C) (b : B →ₗ[A] D) (g : C →ₗ[A] D)
  (ha : Function.Surjective a) (hb : Function.Surjective b)
  (hka : (a.restrictScalars R).ker = I • (⊤ : Submodule R A))
  (hkb : (b.restrictScalars R).ker = I • (⊤ : Submodule R B))
  (hsq : b 1=g (a 1))
  (V : Type u) [AddCommGroup V] [Module A V] [Module R V] [IsScalarTower R A V]

include ha hb hka hkb hsq in
lemma fibreMap_kernel_zero (ell : TorsionLength I) (hds : ell.DirectSumZero)
    (hg : Function.Surjective g) (hTc : powerTorsion I (ModuleCat.of R C))
    (hkg : ell.value (ModuleCat.of R g.ker)=0) :
    ell.value (ModuleCat.of R (fibreMap I (A:=A) (B:=B) V).ker)=0 := by
  sorry

end Square
end Lech.TensorIdeal

end

end OAI
end
