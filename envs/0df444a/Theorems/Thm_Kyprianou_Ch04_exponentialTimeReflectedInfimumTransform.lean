-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exponentialTimeReflectedInfimumTransform
-- name    : Kyprianou.Ch04.exponentialTimeReflectedInfimumTransform
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T22:25:25.343027+00:00
-- url     : https://prove2.me/theorems/969da264-b9bf-4ec3-8d46-dd5e18f9c486
-- title:
--   Theorem 4.8: independent exponential-time drawdown transform
-- statement:
--   The general spectrally negative Levy process X is evaluated at an independent Exp(q) time; for beta>=0 the Laplace transform of its running supremum up to e minus X_e is (q/Phi(q))*(beta-Phi(q))/(psi(beta)-q). The removable singularity beta=Phi(q) is set to q/(Phi(q)*psi'(Phi(q))), with the positive maximal root specified internally.
-- source:
--   Kyprianou (2006), first edition, numbered result 4.8, printed page 99.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
/-- Theorem 4.8 (p. 99). The drawdown is the running supremum minus current value, as printed in Theorem 4.8. Singular beta=Phi(q) uses the derivative limit. -/
theorem exponentialTimeReflectedInfimumTransform
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotNegativeSubordinator :
      ¬ (∀ᵐ omega : Omega ∂P,
        Antitone (fun t : NNReal => L.X t omega)))
    (q : Real) (hq : 0 < q)
    (expTime : Omega → NNReal)
    (heMeasurable : Measurable expTime)
    (heLaw : ∀ t : NNReal,
      (P {omega : Omega | t < expTime omega}).toReal =
        Real.exp (-q * (t : Real)))
    (heIndep :
      Indep
        (MeasurableSpace.comap expTime inferInstance)
        (MeasurableSpace.comap
          (fun omega : Omega => fun t : NNReal => L.X t omega)
          inferInstance) P) :
    ∃ phi : Real,
      0 < phi ∧ L.ψ phi = q ∧
      (∀ theta : Real, 0 ≤ theta → L.ψ theta = q → theta ≤ phi) ∧
      (∀ beta : Real, 0 ≤ beta →
        (if beta = phi then
          (∫ omega, Real.exp (-beta *
            (sSup ((fun s : NNReal => L.X s omega) ''
                Set.Iic (expTime omega)) - L.X (expTime omega) omega)) ∂P) =
            q / (phi * deriv L.ψ phi)
         else
          (∫ omega, Real.exp (-beta *
            (sSup ((fun s : NNReal => L.X s omega) ''
                Set.Iic (expTime omega)) - L.X (expTime omega) omega)) ∂P) =
            (q / phi) * ((beta - phi) / (L.ψ beta - q)))) := by
  sorry
end Kyprianou.Ch04
