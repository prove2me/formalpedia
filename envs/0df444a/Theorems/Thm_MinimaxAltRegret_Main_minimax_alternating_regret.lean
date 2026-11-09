-- Prove2me | Theorems.Thm_MinimaxAltRegret_Main_minimax_alternating_regret
-- name    : MinimaxAltRegret.Main.minimax_alternating_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:56:41.45459+00:00
-- url     : https://prove2.me/theorems/7297b4ea-5e9b-470d-bf0a-380ef768993a
-- title:
--   Theorem 1.1 — tight minimax alternating regret in both settings
-- statement:
--   Alternating regret compares the sum of each loss at the current and next actions to twice its loss at the best fixed hindsight comparator. The goal is the complete quantitative operational form of the two minimax claims. The logarithm is natural unless marked log_2.
--
--   1. For every d>=2 and integer T>=log_2 d, every possibly randomized expert learner admits a fixed oblivious [-1,1]^d sequence with E[R_T^exp]>=floor(log_2 d). For every d>=1 and T>=1, Algorithm 1 at eta=1/10 guarantees R_T^exp<=10 log d on every adaptive sequence.
--   2. The universal constant c=min(1/(480 log 65536),1/4)>0 works for every d>=2 and T>=1: the source's full-dimensional compact convex hard domain is chosen before the learner, and every randomized learner admits a fixed oblivious sequence of continuous convex [0,1] losses with E[R_T]>=c d log(1+T/d).
--   3. On every full-dimensional compact convex domain, for every d>=1 and T>=1, both exact Algorithm 2 options at eta=1/10 satisfy the following, where B=R_T pathwise for Option I and B=E[R_T] for Option II:
--
--   $$B\le4T,\qquad B\le14d\log(1+T/d),\qquad B\le4T\delta+10d\log(1/\delta)\quad\text{for every }0<\delta<1.$$
--
--   Consequently the experts minimax rate is Theta(log d) in the lower-bound horizon regime, and the worst-domain OCO rate is Theta(d log(1+T/d)). Every expectation has the hindsight supremum inside it and is explicitly integrable. All terminal actions use the displayed causal updates; Option II has the exact fresh conditional sampling law. No bound theorem is a hypothesis of the goal.
--
--   **Formalization Note** This conjunction repeats the entire operational content of Theorems 3.1, 3.3, 4.1, and 4.2; it does not assume them. The constants 10, c_0=1/(80 log 65536), c=min(c_0/6,1/4), and 14, together with the delta-family and 4T bound, are the proof instantiations audited in the supporting items.
--
--   Differences from the source:
--   - encoding: rounds 1 through T and the terminal action x_(T+1) → zero-based losses and actions, with action T terminal and source score R_t stored at index t; reason: a bijective reindexing preserves every summand and includes the same terminal update
--   - encoding: a possibly randomized full-information learner and its internal expectation → an arbitrary probability space, a measurable seed-based HistoryLearner on all finite revealed-loss histories, and an explicitly integrable regret random variable; reason: this gives the stated nonanticipating learner and a genuine bounded expectation, with the hindsight supremum inside the integral
--   - encoding: a d-dimensional compact convex set X and convex functions defined on X → a compact convex subset of EuclideanSpace R (Fin d) with nonempty interior, and ambient functions restricted by ConvexOn and pointwise bounds on X; reason: nonempty interior is exactly full affine dimension; arbitrary extensions outside X change no source instance, and no continuity is required on the boundary
--   - encoding: Option II samples from p_t with fresh randomness independent of the committed loss → SampledRun specifies the conditional density law on every pre-sampling event, using a filtration containing past interaction and the committed current loss, and requires measurable regret; reason: the conditional law is the exact sampling operation, contains no performance assumption, and excludes an adversary observing fresh current sampling; integrability is a conclusion
--   - generalization: the two informal Theta-rate characterizations → the full operational lower/upper conjunction with Algorithm 1, both Algorithm 2 options, exact lower witnesses and constants, and the finer delta-family; reason: Theorems 3.1 and 3.3 and Theorems 4.1 and 4.2 supply all clauses; the fixed proof constants imply the stated rates without weakening any constituent claim
--   - encoding: the maximum of expert comparator regret over the simplex → the real sSup of the same comparator-regret image; reason: for d>=1 the finite simplex is nonempty and compact and the comparator objective is continuous, so the maximum is attained and equals this sSup
-- source:
--   Mengxiao Zhang, STOC 2027 submission #57 (October 2026), printed p. 1 / PDF p. 2, Theorem 1.1 (Informal), with Theorems 3.1, 3.3, 4.1, 4.2; SHA-256 6db5a23e9e92d250b4dea7995bf34c9930d39a95df90f5d3fdc715ca26044f31

import Mathlib
import Definitions.Def_MinimaxAltRegret_Main_Experts
import Definitions.Def_MinimaxAltRegret_Main_Sampling
import Definitions.Def_MinimaxAltRegret_Main_LowerConstruction

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace MinimaxAltRegret.Main

theorem minimax_alternating_regret :
  (∀ (d T : ℕ), 2 ≤ d → Real.log (d : ℝ) / Real.log 2 ≤ (T : ℝ) →
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (learner : HistoryLearner (ExpertAction d) (ExpertVector d) Ω),
    ∃ ℓ : ℕ → ExpertVector d, expertLosses d T ℓ ∧
      Integrable (fun ω => expertRegret T ℓ
        (fun t => (response learner ℓ t ω).val)) μ ∧
      (⌊Real.log (d : ℝ) / Real.log 2⌋ : ℤ) ≤
        ∫ ω, expertRegret T ℓ (fun t => (response learner ℓ t ω).val) ∂μ) ∧
  (∀ (d T : ℕ), 0 < d → 0 < T → ∀ ℓ : ℕ → ExpertVector d,
  expertLosses d T ℓ → expertRegret T ℓ (expertAlgorithm T ℓ) ≤ 10*Real.log (d : ℝ)) ∧
  (0 < ocoConstant ∧ ∀ (d T : ℕ), 2 ≤ d → 1 ≤ T →
  ∃ X : Set (Point d), X = hardDomain d T ∧ convexBody X ∧
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (learner : HistoryLearner X (Point d → ℝ) Ω),
      ∃ f : ℕ → Point d → ℝ, continuousLosses01 X T f ∧
        Integrable (fun ω => alternatingRegret X T f
          (fun t => (response learner f t ω).val)) μ ∧
        ocoConstant*(d : ℝ)*Real.log (1+(T : ℝ)/(d : ℝ)) ≤
          ∫ ω, alternatingRegret X T f (fun t => (response learner f t ω).val) ∂μ) ∧
  (∀ (d T : ℕ), 0 < d → 0 < T → ∀ X : Set (Point d), convexBody X →
  ( (∀ f : ℕ → Point d → ℝ, convexLosses X T f →
      (∀ t ≤ T, continuousAlgorithmI X T f t ∈ X) ∧
      continuousUpperBounds d T (alternatingRegret X T f (continuousAlgorithmI X T f))) ∧
    (∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (f : ℕ → Ω → Point d → ℝ) (x : ℕ → Ω → X),
      SampledRun μ X T f x →
      Integrable (fun ω => alternatingRegret X T (fun s => f s ω)
        (fun s => (x s ω).val)) μ ∧
      continuousUpperBounds d T (∫ ω, alternatingRegret X T (fun s => f s ω)
        (fun s => (x s ω).val) ∂μ)))) := by sorry

end MinimaxAltRegret.Main
