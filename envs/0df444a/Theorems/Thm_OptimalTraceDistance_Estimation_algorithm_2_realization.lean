-- Prove2me | Theorems.Thm_OptimalTraceDistance_Estimation_algorithm_2_realization
-- name    : OptimalTraceDistance.Estimation.algorithm_2_realization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T05:44:47.605815+00:00
-- url     : https://prove2.me/theorems/80593c6e-8f63-4c05-9a2d-e2224228303b
-- title:
--   Algorithm 2 — measurability and physical realization
-- statement:
--   The public Keyl report decoder and the spectral report-to-projector map are measurable in the Borel matrix convention. There are universal $C>0$, $d_0\ge2$ such that, for every $d\ge2$ and $0<\varepsilon\le1/32$, a single state-independent normalized POVM on $N$ copies of each input realizes the computed event weights of Algorithm 2, where
--   $$N=\begin{cases}\lceil C_0d^2/\varepsilon^2\rceil,&d<d_0,\\ \lceil C_0d\log^2d\rceil+\lceil CR(d,\varepsilon)\rceil,&d\ge d_0.\end{cases}$$
--   For every input density pair and measurable output event, its Born probability equals the iterated tomography/fresh-spectral expression, including clipping. This records a supporting well-posedness obligation of the stated quantum algorithm, separately from its accuracy estimates.
--
--   Differences from the source:
--   - encoding: Positive-dimensional complex matrices and source trace expressions → Fin d matrices; retained ordered words; real parts of real traces; explicit finite index sums; reason: Indexing and real extraction preserve all source instances; no rank or commutativity restriction is added
--   - encoding: Algorithm 2 is a quantum algorithm with continuous tomography reports → Measurable maps and exact POVM realization of computed event weights are separate theorem obligations; reason: These express physical and measure-theoretic well-posedness without assuming an accuracy, degree, bias or variance guarantee
--   - encoding: Subset-normalized U-statistics of symmetric word kernels → Average over all ordered injective register embeddings; a trailing word coefficient is moved to the first factor by trace cyclicity; reason: Each k-subset occurs k! times in the embedding average, cancelling the identical normalization factor; word traces and symmetric kernels are unchanged
--   - generalization: The report-to-projector map is used on density reports for d≥2 → Its Borel measurability is asserted on the entire ambient complex matrix space in every natural dimension, including d=0 and d=1; reason: The finite spectral indicator has a Borel total extension, equal to zero in dimensions 0 and 1; this adds no input instance or promise to the estimator and specializes to the complete source algorithm
-- source:
--   Ziyun Chen, Minbo Gao, Qisheng Wang, STOC 2027 submission #875 (October 2026), Algorithm 2, p. 11.

import Definitions.Def_OptimalTraceDistance_Estimation_Algorithm2

open MeasureTheory
open scoped BigOperators Matrix Classical ENNReal ComplexOrder
noncomputable section

namespace OptimalTraceDistance.Estimation

theorem algorithm_2_realization :
  (∀ d m : ℕ, ∀ hd : 0 < d, ∀ hm : 0 < m,
    Measurable (fun o : QAlgorithms.Schur.Partition d m × Matrix.unitaryGroup (Fin d) ℂ =>
      QAlgorithms.Schur.estimate hd hm o.1 o.2)) ∧
  (∀ d : ℕ, Measurable (reportProjector d)) ∧
  ∃ C : ℝ, 0 < C ∧ ∃ d₀ : ℕ, 2 ≤ d₀ ∧
    ∀ d : ℕ, 2 ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ 1/32 →
      ∃ M : TwoStateMeasurement d (algorithmCost C d₀ d ε),
        ∀ (ρ σ : Mat d) (hρ : Density ρ) (hσ : Density σ),
          ∀ B : Set ℝ, MeasurableSet B → outcomeLaw M ρ σ hρ hσ B =
            algorithm2Weight C d₀ ε ρ σ hρ hσ B := by sorry

end OptimalTraceDistance.Estimation
