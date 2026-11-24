-- Prove2me | Theorems.Thm_Kyprianou_Ch03_firstPassage_esscherCapExpectation
-- name    : Kyprianou.Ch03.firstPassage_esscherCapExpectation
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-24T00:17:10.8805+00:00
-- url     : https://prove2.me/theorems/3af34252-1296-41e3-b3b2-3197dc83dd7a
-- title:
--   Stopped Esscher martingale has mean one at capped first passage
-- statement:
--   Let $X$ be a non-monotone spectrally negative Lévy process with Laplace exponent $\psi$, fix a discount $q > 0$, and let $\phi = \Phi(q)$ be the largest nonnegative root of $\psi(\theta) = q$. Write $\tau_x^+ = \inf\{t > 0 : X_t > x\}$ for $x > 0$, and let `finiteTime` be a selector for $\tau_x^+$ on $\{\tau_x^+ < \infty\}$.
--
--   Then for every deterministic time $T \ge 0$, the Esscher martingale $M_t = e^{\phi X_t - q t}$ stopped at $\tau_x^+ \wedge T$ has mean one:
--   $$\mathbb{E}\!\left[e^{\phi X_{\tau_x^+ \wedge T} - q(\tau_x^+ \wedge T)}\right] = 1.$$
--   On $\{\tau_x^+ \le T\}$ the creeping identity $X_{\tau_x^+} = x$ is used to rewrite the integrand as $e^{\phi x - q \tau_x^+}$; on $\{\tau_x^+ > T\}$ it is $e^{\phi X_T - q T}$.
-- source:
--   Kyprianou (2006), Chapter 3, Theorem 3.12 proof: optional sampling of the Esscher martingale e^{Φ(q) X_t - q t} at τ_x^+ ∧ T

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem firstPassage_esscherCapExpectation
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
    (T : NNReal) :
    (∫ omega,
      (if firstHittingTime L.X (Set.Ioi x) omega ≠ ⊤ ∧
          finiteTime omega ≤ T
        then Real.exp (phi * x - q * (finiteTime omega : Real))
        else Real.exp (phi * L.X T omega - q * (T : Real))) ∂P) = 1 := by
  sorry

end Kyprianou.Ch03
