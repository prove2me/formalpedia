-- Prove2me | Theorems.Thm_Kyprianou_Ch03_spectrallyNegative_canonicalEsscherUncompleted
-- name    : Kyprianou.Ch03.spectrallyNegative_canonicalEsscherUncompleted
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-23T19:59:15.08613+00:00
-- url     : https://prove2.me/theorems/a270a609-c11d-4398-aaff-7ca1cd61758a
-- statement:
--   Let $X$ be a spectrally negative Lévy process with Laplace exponent $\psi$ defined on a filtered probability space $(\Omega, \mathcal{F}, (\mathcal{F}_t)_{t \ge 0}, \mathbb{P})$, and let $\beta \ge 0$ be an exponential tilting parameter. Then there exists a measurable space $(\Omega_1, \mathcal{F}_1)$ equipped with a filtration $(\mathcal{F}_{1,t})_{t \ge 0}$, probability measures $\mathbb{P}_1$ and $\mathbb{Q}_1$ on $(\Omega_1, \mathcal{F}_1)$, and a spectrally negative Lévy process $L_0$ with respect to $(\mathbb{P}_1, \mathcal{F}_1)$ such that:
--
--   $$\psi_{L_0}(\theta) = \psi(\theta) \quad (\theta \in \mathbb{R}), \qquad \mathbb{Q}_1(A) = \int_A \exp\!\bigl(\beta L_{0,t} - \psi(\beta) t\bigr)\, d\mathbb{P}_1 \quad (t \ge 0,\; A \in \mathcal{F}_{1,t}),$$
--
--   together with preservation of the upward first-passage law — the process $x \mapsto \tau_x^+(L_0) = \inf\{t \ge 0 : L_{0,t} > x\}$ under $\mathbb{P}_1$ has the same law as $x \mapsto \tau_x^+(X)$ under $\mathbb{P}$ — and preservation of the non-monotone-path property (if $X$ does not have $\mathbb{P}$-almost surely non-increasing paths, then $L_0$ does not have $\mathbb{P}_1$-almost surely non-increasing paths).
--
--   This canonical realization decouples the global Esscher change of measure from any ambient probability space: by working on a canonical càdlàg path space with an uncompleted filtration (avoiding global $\mathbb{P}_1$-null completion, which would contradict global singularity $\mathbb{Q}_1 \perp \mathbb{P}_1$ for $\beta > 0$), both the untilted law $\mathbb{P}_1$ and the exponentially tilted law $\mathbb{Q}_1$ coexist as global probability measures on the same space while agreeing with the Esscher density on every $\mathcal{F}_{1,t}$.
--
--   Formalization Note: This lemma replaces the deprecated `Kyprianou.Ch03.spectrallyNegative_canonicalEsscherSpace`, removing the `IsCompletedNaturalFiltration` hypothesis that forces $\mathbb{Q}_1 \ll \mathbb{P}_1$ on the full $\sigma$-algebra.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem spectrallyNegative_canonicalEsscherUncompleted
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (beta : Real) (hBeta : 0 <= beta) :
    exists (Omega1 : Type) (m1 : MeasurableSpace Omega1),
      letI : MeasurableSpace Omega1 := m1
      exists (P1 Q1 : Measure Omega1)
             (hP1 : IsProbabilityMeasure P1)
             (hQ1 : IsProbabilityMeasure Q1)
             (F1 : Filtration NNReal m1)
             (L0 : AvramDividend.Classical.SpectrallyNegativeLevy P1 F1),
        (forall theta : Real, L0.ψ theta = L.ψ theta) ∧
        ((¬ (∀ᵐ omega : Omega ∂ P, Antitone (fun t : NNReal => L.X t omega))) ->
          ¬ (∀ᵐ omega : Omega1 ∂ P1, Antitone (fun t : NNReal => L0.X t omega))) ∧
        Measure.map
          (fun omega : Omega1 =>
            fun x : NNReal =>
              firstHittingTime L0.X (Set.Ioi (x : Real)) omega) P1 =
        Measure.map
          (fun omega : Omega =>
            fun x : NNReal =>
              firstHittingTime L.X (Set.Ioi (x : Real)) omega) P ∧
        (forall (t : NNReal) (A : Set Omega1),
          MeasurableSet[F1 t] A ->
          Q1 A =
            ENNReal.ofReal
              (∫ omega, Set.indicator A
                (fun omega : Omega1 =>
                  esscherDensity L0.X beta (L0.ψ beta) t omega)
                omega ∂P1)) := by
  sorry

end Kyprianou.Ch03
