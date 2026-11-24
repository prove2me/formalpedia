-- Prove2me | Theorems.Thm_Kyprianou_Ch03_firstPassage_esscherCap_trueStoppedMeanOne
-- name    : Kyprianou.Ch03.firstPassage_esscherCap_trueStoppedMeanOne
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-24T01:27:49.908951+00:00
-- url     : https://prove2.me/theorems/87bb1082-de1d-430f-9b45-fa1481fe2e94
-- title:
--   Stopped Esscher martingale at capped first passage has mean one
-- statement:
--   Let $X$ be a non-monotone spectrally negative Lévy process with Laplace exponent $\psi$, fix a discount $q > 0$, and let $\phi = \Phi(q)$ be the largest nonnegative root of $\psi(\theta) = q$. Write $\tau_x^+ = \inf\{t > 0 : X_t > x\}$ for $x > 0$, and let `finiteTime` be a selector for $\tau_x^+$ on $\{\tau_x^+ < \infty\}$.
--
--   For every deterministic time $T \ge 0$, define the capped first-passage time $\tau_x^+ \wedge T$ by using `finiteTime` on $\{\tau_x^+ \le T\}$ and $T$ otherwise. Then the Esscher martingale $M_t = e^{\phi X_t - q t}$ evaluated at the capped time has mean one:
--   $$\mathbb{E}\!\left[e^{\phi X_{\tau_x^+ \wedge T} - q(\tau_x^+ \wedge T)}\right] = 1.$$
--   This is the optional-sampling identity for the Esscher martingale at a bounded stopping time; the position $X_{\tau_x^+ \wedge T}$ is the genuine process value (not yet replaced by the creeping identity $X_{\tau_x^+} = x$).
-- source:
--   Kyprianou (2006), Chapter 3, Theorem 3.12 proof: optional sampling of e^{Φ(q) X_t - q t} at τ_x^+ ∧ T

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem firstPassage_esscherCap_trueStoppedMeanOne
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
      Real.exp (phi *
          (if firstHittingTime L.X (Set.Ioi x) omega ≠ ⊤ ∧
              finiteTime omega ≤ T
            then L.X (finiteTime omega) omega
            else L.X T omega)
        - q *
          (if firstHittingTime L.X (Set.Ioi x) omega ≠ ⊤ ∧
              finiteTime omega ≤ T
            then (finiteTime omega : Real)
            else (T : Real))) ∂P) = 1 := by
  sorry

end Kyprianou.Ch03
