-- Prove2me | Theorems.Thm_Kyprianou_Ch03_spectrallyNegative_esscherCanonicalTilt
-- name    : Kyprianou.Ch03.spectrallyNegative_esscherCanonicalTilt
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-23T19:28:36.417995+00:00
-- url     : https://prove2.me/theorems/58f9c978-1a5a-4861-8cfb-957c58446cda
-- title:
--   Esscher-tilted spectrally negative Lévy process and stopping-time passage identity
-- statement:
--   Let $X = (X_t)_{t \ge 0}$ be a spectrally negative Lévy process on a filtered probability space $(\Omega, \mathcal{F}, P)$ whose sample paths are not almost surely nonincreasing, and let $\phi \ge 0$ be the largest nonnegative root of its Laplace exponent $\psi(\theta) = 0$. For each barrier $x \ge 0$, write $\tau_x^+ = \inf\{t > 0 : X_t > x\}$ for the first upward passage time above $x$.
--
--   Then there exists a filtered probability space $(\Omega_1, \mathcal{F}_1, Q_1)$ supporting a spectrally negative Lévy process $X^{(1)}$ (corresponding to the Esscher tilt of $X$ at parameter $\phi$, with Laplace exponent $\psi_1(\theta) = \psi(\theta + \phi)$) such that:
--   1. $X^{(1)}$ does not have almost surely nonincreasing paths;
--   2. $\theta = 0$ is the unique nonnegative root of $\psi_1(\theta) = 0$; and
--   3. for every barrier $x \ge 0$, every finite set of levels $U \subset [0, x]$, and every family of measurable sets $(B_u)_{u \in U}$ in $[0, \infty]$,
--   $$P\!\left(\{\tau_x^+ < \infty\} \cap \bigcap_{u \in U} \{\tau_u^+ \in B_u\}\right) = e^{-\phi x}\, Q_1\!\left(\bigcap_{u \in U} \{\tau_u^{+,1} \in B_u\}\right),$$
--   where $\tau_u^{+,1} = \inf\{t > 0 : X_t^{(1)} > u\}$.
-- source:
--   Kyprianou (2006), Introductory Lectures on Fluctuations of Lévy Processes with Applications, Chapter 3, §3.3, Corollary 3.10, Theorem 3.12, and Corollary 3.14 (pp. 79–84)

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem spectrallyNegative_esscherCanonicalTilt
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂ P,
      Antitone (fun t : NNReal => L.X t omega)))
    (phi : Real)
    (hRoot : 0 <= phi ∧ L.ψ phi = 0 ∧
      (forall theta : Real, 0 <= theta ->
        L.ψ theta = 0 -> theta <= phi)) :
    exists (Omega1 : Type) (m1 : MeasurableSpace Omega1),
      letI : MeasurableSpace Omega1 := m1
      exists (Q1 : Measure Omega1) (hQ1 : IsProbabilityMeasure Q1)
             (F1 : Filtration NNReal m1)
             (L1 : AvramDividend.Classical.SpectrallyNegativeLevy Q1 F1),
        (¬ (∀ᵐ omega : Omega1 ∂ Q1,
          Antitone (fun t : NNReal => L1.X t omega))) ∧
        (forall theta : Real, 0 <= theta -> L1.ψ theta = 0 -> theta = 0) ∧
        (∀ (x : NNReal) (U : Finset NNReal),
          (∀ u ∈ U, u ≤ x) →
          ∀ (B : NNReal → Set (WithTop NNReal)),
            (∀ u ∈ U, MeasurableSet (B u)) →
            P ({omega : Omega |
                firstHittingTime L.X (Set.Ioi (x : Real)) omega ≠ ⊤} ∩
              ⋂ u ∈ U, {omega : Omega |
                firstHittingTime L.X (Set.Ioi (u : Real)) omega ∈ B u}) =
            ENNReal.ofReal (Real.exp (-phi * (x : Real))) *
              Q1 (⋂ u ∈ U, {omega : Omega1 |
                firstHittingTime L1.X (Set.Ioi (u : Real)) omega ∈ B u})) := by
  sorry

end Kyprianou.Ch03
