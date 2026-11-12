-- Prove2me | Theorems.Thm_MinCostArbPacking_Main_lemma_4_8
-- name    : MinCostArbPacking.Main.lemma_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:45:22.828199+00:00
-- url     : https://prove2.me/theorems/2aa846b4-1753-45fe-94ac-4729ff93056c
-- title:
--   Lemma 4.8 — geometric progress: $O(k\log(kn))$ phases
-- statement:
--   **Lemma 4.8 (Geometric progress).** Assume the standing assumptions of §4.2.
--
--   1. If $\mathrm{def}_I(V)>0$ and $A'$ is a maximal compatible set of terminals, the resulting $I'$ satisfies
--   $$\mathrm{def}_{I'}(V)=\mathrm{def}_I(V)-|A'|\le k|A'| .$$
--   2. Consequently the total deficiency decreases by a factor $k/(k+1)$ in each phase: after $t$ phases of Algorithm 1 started from $I=\emptyset$, it is at most $k(n-1)\big(\tfrac{k}{k+1}\big)^t$.
--   3. There are $O(k\log(kn))$ phases: at most $C\,k\log(kn)$ for an absolute constant $C$.
--
--   This is the progress half of the batching framework.
--
--   **Formalization Note** A phase is the relation `PhaseStep` (standing assumptions, positive deficiency, a proposal system, a maximal compatible set, execution); $C$ is quantified before all graphs.
--
--   Differences from the source:
--   - encoding: the standing assumptions of §3.1 and §4.2 (loops and arcs entering $r$ deleted; $I$ independent, cheapest for its indegree vector, no arc into $r$, indegree $\le k$) → explicit hypotheses `NoLoopNoRootArc` and `Standing`; reason: the source states them once for the whole section; they are hypotheses of every lemma there
--   - encoding: "decreases by a factor $k/(k+1)$ in each phase, and there are $O(k\log(kn))$ phases" → an explicit bound $k(n-1)(k/(k+1))^t$ after $t$ phases from $I=\emptyset$, and $t\le C k\log(kn)$ with one absolute $C$; reason: the source's own count; O(·) read as an absolute constant
-- source:
--   Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), §4.2.3, p.13, Lemma 4.8

import Mathlib
import Definitions.Def_MinCostArbPacking_Main_Exchange
set_option autoImplicit false

namespace MinCostArbPacking.Main

/-- Lemma 4.8 (Geometric progress), p.13: (i) if `def_I(V) > 0` and `A'` is a maximal compatible set
of terminals, then `def_{I'}(V) = def_I(V) - |A'| ≤ k|A'|`; (ii) consequently, after `t` phases of
Algorithm 1 started from `I = ∅`, the total deficiency is at most `k(n-1)(k/(k+1))^t`, and (iii)
there are `O(k log(kn))` phases: at most `C·k·log(kn)` for an absolute constant `C`. -/
theorem lemma_4_8 : ∃ C : ℝ, 0 < C ∧
    (∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : Digraph V E) (k : ℕ) (hk : 1 ≤ k) (r : V) (c : E → ℝ)
    (hG : G.NoLoopNoRootArc r) (I : Finset E) (hI : G.Standing k r c I)
      (u : Finset V → V) (P : Finset V → List E), G.IsProposalSystem k r c I u P →
      0 < G.defiSet k r I Finset.univ → ∀ A', G.MaximalCompatible k r I P A' →
        G.defiSet k r (G.execute k r I P A') Finset.univ =
            G.defiSet k r I Finset.univ - (A'.card : ℤ) ∧
          G.defiSet k r (G.execute k r I P A') Finset.univ ≤ (k : ℤ) * A'.card) ∧
    (∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : Digraph V E) (k : ℕ) (hk : 1 ≤ k) (r : V) (c : E → ℝ)
      (hG : G.NoLoopNoRootArc r) (Iseq : ℕ → Finset E) (t : ℕ), Iseq 0 = ∅ →
      (∀ j, j < t → G.PhaseStep k r c (Iseq j) (Iseq (j + 1))) →
        (G.defiSet k r (Iseq t) Finset.univ : ℝ) ≤
            (k : ℝ) * ((Fintype.card V : ℝ) - 1) * ((k : ℝ) / (k + 1)) ^ t ∧
          (t : ℝ) ≤ C * k * logL ((k : ℝ) * Fintype.card V)) := by sorry

end MinCostArbPacking.Main
