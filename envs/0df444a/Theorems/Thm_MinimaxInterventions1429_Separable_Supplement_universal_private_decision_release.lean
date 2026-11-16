-- Prove2me | Theorems.Thm_MinimaxInterventions1429_Separable_Supplement_universal_private_decision_release
-- name    : MinimaxInterventions1429.Separable.Supplement.universal_private_decision_release
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:18:12.715204+00:00
-- url     : https://prove2.me/theorems/d26be89d-e7ac-4a93-8ca2-6ec2ddcf84dd
-- title:
--   Theorem 1.5 — Universal private decision–release equivalence
-- statement:
--   Let $D$ be any database domain with a specified adjacency relation and any public cube-valued table map $L$. For $m,k\ge2$, every strict linear enlargement $U$, $\varepsilon\ge0$, and $\delta,\beta\in[0,1)$,
--   $$\mathrm{err}_L/17\le\mathrm{dec}_{L,U}\le2\mathrm{err}_L.$$
--   No private entry or contrast is assumed public. A normalized public control can be fixed independently of the database and synopsis. For any private simultaneously accurate synopsis of tolerance $0\le\alpha<1/22$ and any $T\ge1$ with $54\cdot2^{-T}<2-44\alpha$, deterministic reconstruction with failure mapped to zero uses at most $2(mk-1)T$ threshold-bit calls and releases a real table with
--   $$d_q(\widehat L,L)\le17\alpha+\tfrac{51}{2}2^{-T}$$
--   with probability at least $1-\beta$ at every database. Privacy remains $(\varepsilon,\delta)$ on the full domain. The infimal-error inequalities assume no attained infimum.
--
--   Differences from the source:
--   - encoding: arbitrary synopses and private errors → arbitrary measurable spaces, measurable success events, real infima, and a total literal finite-call release; reason: no attainment is assumed; zero replaces failure and finite bit branching makes postprocessing measurable
--   - encoding: m and k indexed from 1, with m,k >= 2 → Fin m and Fin k indexed from 0, with explicit nonzero instances and m,k >= 2; reason: source column 1 is Lean column 0; dimensions and closed-simplex boundary instances are preserved
-- source:
--   chaomeng chen, STOC 2027 submission #1429 (October 2026), Theorem 1.5, printed p.4 (PDF p.6)

import Definitions.Def_MinimaxInterventions1429_Separable_Supplement_Privacy
set_option autoImplicit false
universe u_universal_private_decision_release

noncomputable section

namespace MinimaxInterventions1429.Separable.Supplement
open MeasureTheory

theorem universal_private_decision_release
    {D : Type u_universal_private_decision_release} {m k : ℕ} [NeZero m] [NeZero k] (hm : 2 ≤ m) (hk : 2 ≤ k)
    (adj : D → D → Prop) (L : D → Table m k) (hL : ∀ d, InCube (L d))
    (U : Submodule ℝ (Table m k)) (hU : separableSpace m k < U)
    (ε δ β : ℝ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ ∧ δ < 1) (hβ : 0 ≤ β ∧ β < 1) :
    (releaseError adj L ε δ β / 17 ≤ decisionError adj L (enlargedQueries U) ε δ β ∧
      decisionError adj L (enlargedQueries U) ε δ β ≤ 2*releaseError adj L ε δ β) ∧
    ∃ C : Table m k, C ∈ U ∧ (∀ g, C g 0 = 0) ∧ entryNorm C = 1 ∧ interaction C = 2 ∧
      ∀ (S : Type u_universal_private_decision_release) [MeasurableSpace S] (syn : Synopsis S m k) (law : D → Measure S)
        (α : ℝ) (T : ℕ), 0 ≤ α → α < 1/22 → 1 ≤ T → 54*eta T < 2-44*α →
        PrivateSynopsis adj L (enlargedQueries U) ε δ β α syn law →
        (twoShift C 1 α T).maxQueries ≤ 2*(m*k-1)*T ∧
        Measurable (totalShiftOutput syn.decode C 1 α T) ∧
        (let out := fun d => (law d).map (totalShiftOutput syn.decode C 1 α T)
         (∀ d, IsProbabilityMeasure (out d)) ∧ DifferentiallyPrivate adj ε δ out ∧
           ReleaseAccurate L out β (17*α+(51/2)*eta T)) := by sorry

end MinimaxInterventions1429.Separable.Supplement
