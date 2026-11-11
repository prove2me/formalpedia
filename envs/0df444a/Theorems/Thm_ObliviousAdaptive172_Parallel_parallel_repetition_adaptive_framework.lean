-- Prove2me | Theorems.Thm_ObliviousAdaptive172_Parallel_parallel_repetition_adaptive_framework
-- name    : ObliviousAdaptive172.Parallel.parallel_repetition_adaptive_framework
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:57:36.600928+00:00
-- url     : https://prove2.me/theorems/845873f1-6792-4246-abb4-c15224e65c94
-- title:
--   Theorem 1.1 — parallel repetition adaptive framework
-- statement:
--   Fix desired confidence $c>0$ and the primitive's original runtime-confidence exponent $b>0$. There are positive constants $C_{\rm copies},C_{\rm work}$ and a threshold $N\ge2$, depending only on these exponents, such that the following holds uniformly over $n\ge N$, every legal dynamic history model, every configuration space $W$, every finite horizon $m$, and every weak stable-certifying primitive for $P\Rightarrow P'$ with actual budget $T_A$.
--
--   The operational Algorithm 2 compiler runs $L=\lceil64(c+1)\ln n\rceil$ independent copies. For every legal adaptive adversary observing only published outputs, including independently randomized adversaries, a single event of probability at least $1-n^{-c}$ satisfies, simultaneously at all delivered steps including initialization,
--
--   $$
--   \begin{gathered}
--   L\le C_{\rm copies}\ln n,\qquad
--   T_{\rm wrapper}\le C_{\rm work}T_A\ln n,\\
--   \neg P'(G_t)\Longrightarrow \operatorname{out}_t=\text{“no”},\qquad
--   P(G_t)\Longrightarrow \operatorname{out}_t=w\text{ for a valid }P'\text{-configuration }w.
--   \end{gathered}
--   $$
--
--   Every published configuration is stable on every legal continuation. On all runs, independently of the success event, once a configuration is published every later answer is that identical configuration: output changes at most once. Thus the approximation is exactly the primitive's relaxed witness relation, with no change to its factor or its configuration domain. The theorem asserts the full compiler and its total executed work, rather than only the existence of a successful witness.
--
--   **Formalization Note** All constants and the threshold precede the size, state spaces, primitive, stream horizon and adversary. The source's $64d$ repetition coefficient is instantiated with $d=c+1$, and its done guard remains $1/4$. The source proof's intermediate quantile is $1/8$; it is an analysis parameter, not a compiler input. A sufficient asymptotic threshold also makes $n^{-b}\le1/8$. No $n^{-(c+2)}$ runtime tail, simultaneous primitive completeness, or conditional copy independence is assumed. Only measurability of the induced probability events is made explicit. Initialization is action zero, work includes input delivery, instructions and wrapper control, and returning a frozen witness uses a handle. Arbitrary update and witness spaces and arbitrary seed laws are permitted; infinite primitive computation has infinite cost and is interrupted by the compiler. The public adversary cannot inspect any internal counter or stored witness before triggering.
--
--   Differences from the source:
--   - generalization: graph states and legal incremental or decremental updates → arbitrary legal history transition systems, with graph histories as instances; reason: no graph instance is excluded, and the history-dependent synthetic property in §3.3 is expressible
--   - encoding: a randomized dynamic algorithm with internal storage and update time → a causal private-tape instruction machine, actual witness-handle memory and executed instruction costs, with divergence assigned infinite cost; reason: this exposes computation and storage rather than accepting either as an arbitrary supplied certificate
--   - encoding: probabilities over independent private randomness and an output-observing adaptive adversary → arbitrary probability measures, their actual product law, measurable witnessing success events and explicit measurability of induced execution events; reason: the source probability assertions presuppose measurable events; this adds no probability, correctness or runtime bound and imposes no finite-support condition
--   - generalization: the same displayed confidence exponent c in the primitive runtime contract and the wrapper guarantee → any primitive runtime exponent b greater than zero and any desired final exponent c greater than zero; reason: setting b equal to c recovers the headline; repetition can amplify fixed constant completeness without assuming the stronger n^(-(c+2)) primitive tail used in Appendix B.1
--   - encoding: a finite stream and its first property-holding step → arbitrary finite horizons, policies allowed to stop, initialization as action zero and an optional first hit; reason: the empty or initially satisfying stream is retained; when there is no hit, prefix runtime covers the entire delivered stream without a false storage deadline
--   - encoding: O(log n) copies and O(T_A log n) work, with L=ceil(64 d ln n) in Algorithm 2 → L=ceil(64(c+1) ln n), and positive copy/work constants and a size threshold chosen before every instance, primitive, horizon and policy; reason: d is instantiated as c+1; asymptotic constants may depend only on c and b, the original primitive exponent is unchanged, and small sizes are handled by the uniform asymptotic threshold
--   - generalization: bounded output complexity included in the headline high-probability guarantee → the identical-output-after-trigger property holds for every tape and every history extension, independently of the success event; reason: the triggered branch preserves the stored witness on every subsequent action; this unconditional control invariant implies the source clause on its high-probability event
-- source:
--   Shiri Chechik, Inbal Hadad, From Oblivious to Adaptive Adversaries: Black-Box Reductions for Monotone Dynamic Problems with Applications to Cuts, Distances, and Clustering, STOC 2027 submission #172 (October 2026), pp. 2–3, Theorem 1.1 (PDF pp. 4–5); p. 12, Algorithm 2 (PDF p. 14); pp. 28–29, Appendix B.1 (PDF pp. 30–31)

import Mathlib
import Definitions.Def_ObliviousAdaptive172_Parallel_parallelWrapper
set_option autoImplicit false

namespace ObliviousAdaptive172.Parallel

open MeasureTheory

/-- Full Theorem 1.1, printed pp.2–3 (PDF pp.4–5). The compiler is Algorithm 2.
Uniform constants precede every instance, primitive, horizon, and adversary. Only the
primitive's original runtime tail is assumed; `b` is never replaced by `c+2`.
There is one joint success event for all outputs and total *executed* work. -/
theorem parallel_repetition_adaptive_framework :
    ∀ (c b : ℝ), 0 < c → 0 < b →
    ∃ Ccopies Cwork : ℝ, 0 < Ccopies ∧ 0 < Cwork ∧
    ∃ N : ℕ, 2 ≤ N ∧
    ∀ n : ℕ, N ≤ n →
    ∀ (U W R Q : Type)
      [MeasurableSpace R] (μ : Measure R) [IsProbabilityMeasure μ]
      (M : HistoryModel U) (exactProperty : List U → Prop) (valid : List U → W → Prop)
      (A : PrivateTapeExecution U W R Q) (T m : ℕ),
      WeakStableCertifying M exactProperty valid μ A n b T m →
      let L := repetitions c n
      (L : ℝ) ≤ Ccopies * Real.log (n : ℝ) ∧
      (∀ (tapes : Fin L → R) (h e : List U) (w : W),
        (parallelWrapper A L T tapes h).answer = some w →
        (parallelWrapper A L T tapes (h ++ e)).answer = some w) ∧
      ∀ (Ξ : Type) [MeasurableSpace Ξ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
        (π : OutputPolicy U W Ξ), AdmissiblePolicy M π →
        let H := fun z : (Fin L → R) × Ξ =>
          (interact (fun h => some (parallelWrapper A L T z.1 h).answer) π z.2 m).history
        ExecutionEventsMeasurable H
          (fun z h => (parallelWrapper A L T z.1 h).answer)
          (fun z h => ((parallelWrapper A L T z.1 h).work : ℕ∞)) exactProperty
          (fun z h => ∃ w, (parallelWrapper A L T z.1 h).answer = some w ∧ valid h w) →
        WithProbability ((Measure.pi (fun _ : Fin L => μ)).prod ν)
          (1 - (n : ℝ) ^ (-c)) (fun z =>
            let h := H z
            ((parallelWrapper A L T z.1 h).work : ℝ) ≤ Cwork * T * Real.log (n : ℝ) ∧
            ∀ t ≤ h.length,
              let hist := h.take t
              let out := (parallelWrapper A L T z.1 hist).answer
              (¬ (∃ w, valid hist w) → out = none) ∧
              (exactProperty hist → ∃ w, out = some w ∧ valid hist w) ∧
              (∀ w, out = some w → valid hist w ∧ M.Stable valid hist w)) := by sorry

end ObliviousAdaptive172.Parallel
