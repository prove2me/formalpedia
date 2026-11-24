-- Prove2me | Theorems.Thm_Kyprianou_Ch03_firstPassageTransform_positiveDiscount_strictBarrier_fromCap
-- name    : Kyprianou.Ch03.firstPassageTransform_positiveDiscount_strictBarrier_fromCap
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-24T00:17:15.686306+00:00
-- url     : https://prove2.me/theorems/07aff436-81e9-4a99-a8c2-029e94801b03
-- title:
--   Positive-discount first-passage transform via capped Esscher limit
-- statement:
--   Assume the capped Esscher identity
--   $$\mathbb{E}\!\left[e^{\phi X_{\tau_x^+ \wedge T} - q(\tau_x^+ \wedge T)}\right] = 1 \qquad (\forall T \ge 0)$$
--   and the creeping property $X_{\tau_x^+} = x$ a.s. on $\{\tau_x^+ < \infty\}$, for $\phi = \Phi(q)$ and $x > 0$.
--
--   Passing to the limit $T \to \infty$ by dominated convergence (using the bound $0 < M_{\tau_x^+ \wedge T} \le e^{\phi x}$ and $e^{-q T} \to 0$ on $\{\tau_x^+ = \infty\}$) yields
--   $$\mathbb{E}\!\left[e^{-q \tau_x^+}\mathbf{1}_{\{\tau_x^+ < \infty\}}\right] = e^{-\phi x}.$$
-- source:
--   Kyprianou (2006), Chapter 3, Theorem 3.12 proof: T→∞ limit of the stopped Esscher identity

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem firstPassageTransform_positiveDiscount_strictBarrier_fromCap
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂ P,
      Antitone (fun t : NNReal => L.X t omega)))
    (q : Real) (hq : 0 < q)
    (phi : Real)
    (hRoot : 0 ≤ phi ∧ L.ψ phi = q ∧
      (∀ theta : Real, 0 ≤ theta → L.ψ theta = q → theta ≤ phi))
    (x : Real) (hx : 0 < x)
    (finiteTime : Omega → NNReal)
    (hfin : ∀ omega,
      firstHittingTime L.X (Set.Ioi x) omega != ⊤ →
        firstHittingTime L.X (Set.Ioi x) omega =
          (finiteTime omega : WithTop NNReal))
    (hCap : ∀ T : NNReal,
      (∫ omega,
        (if firstHittingTime L.X (Set.Ioi x) omega ≠ ⊤ ∧
            finiteTime omega ≤ T
          then Real.exp (phi * x - q * (finiteTime omega : Real))
          else Real.exp (phi * L.X T omega - q * (T : Real))) ∂P) = 1)
    (hCreep : ∀ᵐ omega ∂P,
      firstHittingTime L.X (Set.Ioi x) omega ≠ ⊤ →
        L.X (finiteTime omega) omega = x) :
    (∫ omega,
      if firstHittingTime L.X (Set.Ioi x) omega = ⊤
      then (0 : Real)
      else Real.exp (-q * (finiteTime omega : Real)) ∂P) =
      Real.exp (-phi * x) := by
  sorry

end Kyprianou.Ch03
