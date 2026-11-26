-- Prove2me | Theorems.Thm_Kyprianou_Ch05_tailLaplaceAsymptotics
-- name    : Kyprianou.Ch05.tailLaplaceAsymptotics
-- status  : Open
-- author  : @daga2
-- created : 2026-11-26T03:14:37.438091+00:00
-- url     : https://prove2.me/theorems/74e702c3-7665-526d-878c-86af7ad2c07b
-- title:
--   Lemma 5.17, step 2: Laplace asymptotics of the Lévy tail density
-- statement:
--   Let $\bar\Pi(x) = \Pi((x,\infty))$ be the tail of the Lévy measure of an unkilled subordinator with Laplace exponent $\Phi$ and drift $d$. Viewed as a density on $[0,\infty)$, its Laplace transform is $(\Phi(\theta) - d\theta)/\theta$. For $\alpha < 1$, if $\Phi$ is regularly varying of index $\alpha$, then this Laplace transform has the Karamata form: the ratio of the Laplace transform to $\theta^{-(1-\alpha)} L(1/\theta)$ tends to $1$, as $\theta \to 0^+$ when $\Phi$ is regularly varying at $0$, and as $\theta \to \infty$ when $\Phi$ is regularly varying at $\infty$, where $L$ is the slowly varying factor determined by $\Phi$. The drift term is negligible: at $0$ it is $o(\Phi(\theta))$, and at $\infty$ regular variation of index $< 1$ forces $d = 0$. The tail $\bar\Pi$ is antitone, hence ultimately monotone in both senses used by the monotone-density theorems.
--
--   This is the analytic input that the Karamata monotone-density theorems (Theorems 5.14 and 5.15) convert into the Lévy-tail limits of Lemma 5.17.
--
--   **Formalization Note** The tail measure is the volume measure on $[0,\infty)$ with density $x \mapsto \bar\Pi(x)$; its support and monotonicity facts are packaged with the Laplace asymptotic.
-- source:
--   Kyprianou (2006), Fluctuations of Lévy Processes with Applications, first edition, Lemma 5.17, printed pp. 121, 130 or 132; Theorems 5.13-5.15, p. 127.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_MonotoneDensity
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Lemma 5.17, step 2 (tail): the Lévy tail, as a density on
`[0, ∞)`, has Laplace transform `(Phi theta - d * theta) / theta`,
and for `alpha < 1` regular variation of `Phi` transports to a
Karamata-ready Laplace asymptotic, at both endpoints. The drift term
is negligible: at zero it is `o(Phi theta)`, and at infinity regular
variation of index `< 1` forces `d = 0`. The tail is antitone, hence
ultimately monotone in both senses used by Theorems 5.14 / 5.15. -/
theorem tailLaplaceAsymptotics
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : IsKilledSubordinator P Y death 0)
    (hTriplet : IsKilledLaplaceTriplet 0 d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * Phi theta))
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U)
    (alpha : Real) (hAlpha : 0 ≤ alpha ∧ alpha ≤ 1) (hAlpha1 : alpha < 1) :
  ((RegularlyVaryingAtZero Phi alpha →
     ∃ L : Real → Real, SlowlyVaryingAtInfinity L ∧
       (∀ x : Real, 0 < x → Phi (1 / x) = x ^ (-alpha) * L x) ∧
       UltimatelyMonotone (fun x : Real => (Pi (Set.Ioi x)).toReal) ∧
       UltimatelyMonotoneAtZero (fun x : Real => (Pi (Set.Ioi x)).toReal) ∧
       ((((volume : Measure Real).restrict (Set.Ici (0 : Real))).withDensity
           (fun x : Real => ENNReal.ofReal ((Pi (Set.Ioi x)).toReal)))
         (Set.Iio (0 : Real)) = 0) ∧
       Tendsto
         (fun theta : Real =>
           (positiveLaplace
             (((volume : Measure Real).restrict (Set.Ici (0 : Real))).withDensity
               (fun x : Real => ENNReal.ofReal ((Pi (Set.Ioi x)).toReal))) theta).toReal /
             (theta ^ (-(1 - alpha)) * L (1 / theta)))
         (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 1)) ∧
   (RegularlyVaryingAtInfinity Phi alpha →
     ∃ L : Real → Real, SlowlyVaryingAtZero L ∧
       (∀ x : Real, 0 < x → Phi (1 / x) = x ^ (-alpha) * L x) ∧
       UltimatelyMonotone (fun x : Real => (Pi (Set.Ioi x)).toReal) ∧
       UltimatelyMonotoneAtZero (fun x : Real => (Pi (Set.Ioi x)).toReal) ∧
       ((((volume : Measure Real).restrict (Set.Ici (0 : Real))).withDensity
           (fun x : Real => ENNReal.ofReal ((Pi (Set.Ioi x)).toReal)))
         (Set.Iio (0 : Real)) = 0) ∧
       Tendsto
         (fun theta : Real =>
           (positiveLaplace
             (((volume : Measure Real).restrict (Set.Ici (0 : Real))).withDensity
               (fun x : Real => ENNReal.ofReal ((Pi (Set.Ioi x)).toReal))) theta).toReal /
             (theta ^ (-(1 - alpha)) * L (1 / theta)))
         atTop (nhds 1))) := by
  sorry

end Kyprianou.Ch05
