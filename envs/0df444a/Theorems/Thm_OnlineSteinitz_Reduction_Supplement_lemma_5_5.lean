-- Prove2me | Theorems.Thm_OnlineSteinitz_Reduction_Supplement_lemma_5_5
-- name    : OnlineSteinitz.Reduction.Supplement.lemma_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:21:28.846846+00:00
-- url     : https://prove2.me/theorems/85d039cd-aafb-4609-ab0c-08eb1e5567df
-- title:
--   Lemma 5.5 — randomized dimension lower bound for all failure parameters
-- statement:
--   There exists an absolute constant $c>0$ such that for every $T\ge2$, $d\ge1$, $0<\delta<1$, real radius $\rho$, and randomized causal ordering algorithm, if every fixed zero-sum unit-ball input has success probability at least $1-\delta$ at radius $\rho$, then, with $d_*=\min(d,T)$,
--
--   $$\rho\ge c(1-\delta)\sqrt{d_*\log(T/d_*)}.$$
--
--   The constant is independent of all algorithmic and numerical parameters. The logarithm is the printed $\log(T/d_*)$, rather than the stronger $\log(2+T/d_*)$ appearing in the proof. In particular the printed dimension term vanishes when $d\ge T$. This supplies the dimension term of Theorem 5.1.
--
--   Differences from the source:
--   - encoding: real Euclidean vectors and positions numbered 1 through T → the published Vec d and Run types with zero-based positions and Fin T arrivals; reason: the index shift preserves all streams, placements and prefixes including 0 and T
--   - encoding: arbitrary deterministic or randomized immediate ordering algorithms → history-dependent slot rules with validity on every promised stream; arbitrary private probability spaces and measurable fixed-history decisions; reason: full private tapes model persistent state and dependent randomness; no future input or discrepancy property is assumed
--   - encoding: the optimal discrepancy bounds OSdet and OSrand → operational achievable guarantees, with one absolute constant before all instance parameters; reason: upper bounds exhibit a fixed causal rule; lower bounds apply to every valid rule and every uniformly achievable real radius, without assuming an attained optimum
-- source:
--   Russo–Wei, The Online Steinitz Problem, STOC 2027 submission #22 (2026 preprint), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/22.pdf; SHA-256 32ff14f15a94c95630765c77f4fa5a429fb294bcf03a9055ed67c60658769366; Lemma 5.5, PDF/printed p.23 (proof continues on the following pages)

import Definitions.Def_OnlineSteinitz_Reduction_Supplement_Bounds

open MeasureTheory

namespace OnlineSteinitz.Reduction.Supplement

/-- Lemma 5.5, p.23; the displayed log(T/d*) is retained, not the stronger proof variant. -/
theorem lemma_5_5 :
    ∃ c : ℝ, 0 < c ∧ ∀ (T d : ℕ), 2 ≤ T → 1 ≤ d →
      ∀ (δ ρ : ℝ), 0 < δ → δ < 1 →
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (A : OrderingRule d Ω), ValidOrdering (T := T) A → MeasurableOrdering A →
        RandomizedGuarantee (T := T) μ A δ ρ →
        c * (1 - δ) * dimensionRate T d ≤ ρ := by sorry

end OnlineSteinitz.Reduction.Supplement
