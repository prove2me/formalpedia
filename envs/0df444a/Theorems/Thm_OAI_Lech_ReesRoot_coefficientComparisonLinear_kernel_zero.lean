-- Prove2me | Theorems.Thm_OAI_Lech_ReesRoot_coefficientComparisonLinear_kernel_zero
-- name    : OAI.Lech.ReesRoot.coefficientComparisonLinear_kernel_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:53:21.628424+00:00
-- url     : https://prove2.me/theorems/a525f1f1-e0e4-4464-b5da-b691e026fa5b
-- title:
--   OAI.Lech.ReesRoot.coefficientComparisonLinear_kernel_zero: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech.ReesRoot`, with `open CategoryTheory IdealGraded HomogeneousLocalization`, `open scoped TensorProduct`):
--
--   ```lean
--   lemma coefficientComparisonLinear_kernel_zero (ell : TorsionLength I) (hds : ell.DirectSumZero)
--       (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
--       (ha : ∀ a : ℕ,0<a → ell.value
--         (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=
--           a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))
--       (s : Finset (Fin (n+1))) :
--       ell.value (ModuleCat.of R (coefficientComparisonLinear I z hz hgen s).ker)=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.TorsionLength` (definitions bundle `OAIQ032L000` of this split); `OAI.Lech.SourceGraded.sourceGrade` (definitions bundle `OAIQ032L002` of this split); `OAI.Lech.Homogeneous.awayAddCommGroup`, `OAI.Lech.ProjectiveCoefficientChart.grading`, `OAI.Lech.ProjectiveRoot.Ring` and `OAI.Lech.ProjectiveRoot.product` (definitions bundle `OAIQ032L004` of this split); `OAI.Lech.SourceGraded.source_graded` (definitions bundle `OAIQ032L011` of this split); `OAI.Lech.TorsionLength.DirectSumZero` (definitions bundle `OAIQ032L017` of this split); `OAI.Lech.ReesRoot.CoefficientRing`, `OAI.Lech.ReesRoot.ExceptionalRing`, `OAI.Lech.ReesRoot.coefficientDenominator`, `OAI.Lech.ReesRoot.coefficientTower`, `OAI.Lech.ReesRoot.coefRing`, `OAI.Lech.ReesRoot.coefficientPModule` and `OAI.Lech.ReesRoot.exRing` (definitions bundle `OAIQ032L022` of this split); `OAI.Lech.ReesRoot.coefficientComparisonLinear` and `OAI.Lech.ReesRoot.exceptionalPModule` (definitions bundle `OAIQ032L026` of this split); `OAI.Lech.ReesRoot.coefModule` (definitions bundle `OAIQ032L027` of this split).
--
--   **Used by.** The proof of `OAI.Lech.ReesRoot.fibreCech_homology` of this split imports it.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ032L026
import Definitions.Def_OAIQ032L027

section

attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory IdealGraded HomogeneousLocalization
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (hgen : Ideal.span (Set.range z)=I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup

attribute [local instance] OAI.Lech.ReesRoot.coefRing
attribute [local instance] OAI.Lech.ReesRoot.exRing
attribute [local instance] OAI.Lech.ReesRoot.coefModule
attribute [local instance] OAI.Lech.ReesRoot.coefficientPModule
attribute [local instance] OAI.Lech.ReesRoot.exceptionalPModule
lemma coefficientComparisonLinear_kernel_zero (ell : TorsionLength I) (hds : ell.DirectSumZero)
    (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
    (ha : ∀ a : ℕ,0<a → ell.value
      (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=
        a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))
    (s : Finset (Fin (n+1))) :
    ell.value (ModuleCat.of R (coefficientComparisonLinear I z hz hgen s).ker)=0 := by
  sorry

end Lech.ReesRoot

end

end OAI
end
