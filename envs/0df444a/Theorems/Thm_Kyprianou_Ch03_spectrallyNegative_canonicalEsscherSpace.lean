-- Prove2me | Theorems.Thm_Kyprianou_Ch03_spectrallyNegative_canonicalEsscherSpace
-- name    : Kyprianou.Ch03.spectrallyNegative_canonicalEsscherSpace
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T19:49:49.34805+00:00
-- url     : https://prove2.me/theorems/2028f681-e8b5-47ab-abe9-45b015894127
-- title:
--   Canonical space and global Esscher measure for a spectrally negative Lévy process
-- statement:
--   Let $X = (X_t)_{t \ge 0}$ be a spectrally negative Lévy process on a filtered probability space $(\Omega, \mathcal{F}, P)$ with Laplace exponent $\psi$, and let $\beta \ge 0$.
--
--   Then there exists a canonical measurable space $(\Omega_1, \mathcal{G}_1)$ equipped with two probability measures $P_1, Q_1$, the $P_1$-completed natural filtration $\mathcal{F}_1 = (\mathcal{F}_{1,t})_{t \ge 0}$, and a spectrally negative Lévy process $X^{(0)}$ under $P_1$ such that:
--   1. $X^{(0)}$ has the same Laplace exponent $\psi_0(\theta) = \psi(\theta)$ for all $\theta \in \mathbb{R}$, retains non-antitone sample paths whenever $X$ does, and has the same $[0, \infty]^{[0, \infty)}$-valued upward first-passage law as $X$; and
--   2. $Q_1$ is a global Esscher-tilted probability measure satisfying, for every $t \ge 0$ and every $A \in \mathcal{F}_{1,t}$,
--   $$Q_1(A) = \int_A \exp\!\bigl(\beta X_t^{(0)} - \psi(\beta) t\bigr)\, dP_1.$$
--
--   This canonical realization bridges an arbitrary spectrally negative Lévy process to the Kolmogorov-extended global Esscher probability space required by Corollary 3.10 and Corollary 3.14 of Kyprianou (2006).
-- source:
--   Kyprianou (2006), Introductory Lectures on Fluctuations of Lévy Processes with Applications, Chapter 3, §3.3, Theorem 3.9 and Corollary 3.10 (pp. 76–80)

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem spectrallyNegative_canonicalEsscherSpace
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
        IsCompletedNaturalFiltration P1 L0.X F1 ∧
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
