-- Prove2me | Theorems.Thm_Kyprianou_Ch03_firstPassage_esscherCap_meanOne_of_rightContStoppingTime
-- name    : Kyprianou.Ch03.firstPassage_esscherCap_meanOne_of_rightContStoppingTime
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-24T01:43:40.53322+00:00
-- url     : https://prove2.me/theorems/8ba170a7-d847-49bb-b9ce-6019729588e5
-- title:
--   Esscher mean one given capped first-passage is an $F_+$-stopping time
-- statement:
--   Let $X$ be a spectrally negative Lévy process, $q>0$, and $\phi=\Phi(q)$. For a barrier $x>0$, selector `finiteTime` of $\tau_x^+$, and horizon $T\ge 0$, write $\sigma=\tau_x^+\wedge T$ for the capped first-passage time built from `finiteTime`.
--
--   Assume $\sigma$ is a stopping time of the right-continuous filtration $\mathcal{F}_+$ and that $\sigma\le T$ pathwise. Then the Esscher martingale evaluated at $\sigma$ has mean one:
--   $$\mathbb{E}\!\left[e^{\phi X_\sigma - q\sigma}\right]=1.$$
--
--   This is the optional-sampling / likelihood mean-one identity specialised to the capped first-passage time; it follows from the general bounded-stopping-time Esscher mean-one theorem for spectrally negative Lévy processes.
-- source:
--   Kyprianou (2006), Ch.3 Thm 3.12; AvramDividend.Classical.avram_p4_f_assembly_original_rightCont_bounded_stop_esscher_likelihood_mean_one

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem firstPassage_esscherCap_meanOne_of_rightContStoppingTime
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
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
    (T : NNReal)
    (hstop : IsStoppingTime F.rightCont
      (fun omega =>
        ((if firstHittingTime L.X (Set.Ioi x) omega ≠ ⊤ ∧
            finiteTime omega ≤ T
          then finiteTime omega
          else T) : WithTop NNReal)))
    (hbound : ∀ omega,
      (if firstHittingTime L.X (Set.Ioi x) omega ≠ ⊤ ∧
          finiteTime omega ≤ T
        then finiteTime omega
        else T) ≤ T) :
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
