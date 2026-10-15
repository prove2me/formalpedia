-- Prove2me | Theorems.Thm_OnlineMaxWeightMatch_Approx_lemma_4_4
-- name    : OnlineMaxWeightMatch.Approx.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:51:51.519431+00:00
-- url     : https://prove2.me/theorems/2e8ff938-5eab-4cb3-b78c-704414b25501
-- title:
--   Lemma 4.4: first-pick matching probabilities Pr[(i,t) ∈ M1]
-- statement:
--   **Standing setting (§4).** $I$ is a RideHail instance with bins $i\in\iota$ (a finite set) and balls $t=1,\dots,n$, arrival probabilities $p_t\in[0,1]$ and weights $w_{i,t}\ge 0$. The vector $x=(x_{i,t})$ is a feasible solution of LP-Match (constraints (9)–(12)) that satisfies Constraint (10) with equality, $\sum_i x_{i,t}=p_t$ for every ball $t$ (the paper's standing assumption, guaranteed by the dummy bins of Line 2 of Algorithm 1). Algorithm 1 (Lines 3–13) is run on $x$ with $c=0.01$; $\Pr$ is the probability over its randomness (arrivals, first picks, acceptance coins, second picks).
--
--   Let $M_1$ be the set of edges added in Line 8 (first picks). Then:
--   1. for every early edge $(i,t)$,
--   $$
--   \Pr[(i,t)\in M_1]=x_{i,t}\cdot(1/2+c);
--   $$
--   2. for every edge $(i,t)$,
--   $$
--   x_{i,t}\cdot(1/2-3c)\ \le\ \Pr[(i,t)\in M_1]\ \le\ x_{i,t}\cdot(1/2+c).
--   $$
--
--   This is the analysis of the first pick: early edges are matched with exactly the target probability, late ones with nearly half of it. Theorem 4.6 supplies the missing $4c$ for late edges.
--
--   **Formalization Note** "Early" is Definition 4.3; every pair $(i,t)$ is an edge (missing edges have weight $0$).
-- source:
--   Papadimitriou, Pollner, Saberi & Wajc, Online Stochastic Max-Weight Bipartite Matching: Beyond Prophet Inequalities, arXiv:2102.10261v3, p. 12, Lemma 4.4

import Mathlib
import Definitions.Def_OnlineMaxWeightMatch_Approx_Analysis

open MeasureTheory ProbabilityTheory

namespace OnlineMaxWeightMatch.Approx

/-- Lemma 4.4. Run Algorithm 1 (Lines 3–13) on an LP-Match feasible `x` with `Σ_i x_{i,t} = p_t`
for every ball `t`. If edge `(i, t)` is early, `Pr[(i, t) ∈ M1] = x_{i,t} · (1/2 + c)`; for every
edge, `x_{i,t} · (1/2 - 3c) ≤ Pr[(i, t) ∈ M1] ≤ x_{i,t} · (1/2 + c)`. -/
theorem lemma_4_4 {ι : Type*} [Fintype ι] {n : ℕ} (I : RideHailInstance ι n)
    (x : ι → Fin n → ℝ) (hx : LPFeasible I x) (htight : ∀ t, ∑ i, x i t = I.p t)
    :
    (∀ i t, IsEarly x i t →
      (algMeasure I x).real {ω | (i, t) ∈ M1 x ω} = x i t * (1 / 2 + c)) ∧
    (∀ i t, x i t * (1 / 2 - 3 * c) ≤ (algMeasure I x).real {ω | (i, t) ∈ M1 x ω} ∧
      (algMeasure I x).real {ω | (i, t) ∈ M1 x ω} ≤ x i t * (1 / 2 + c)) := by sorry

end OnlineMaxWeightMatch.Approx
