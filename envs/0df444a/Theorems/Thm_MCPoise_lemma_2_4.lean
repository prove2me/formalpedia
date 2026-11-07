-- Prove2me | Theorems.Thm_MCPoise_lemma_2_4
-- name    : MCPoise.lemma_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:33:24.959845+00:00
-- url     : https://prove2.me/theorems/b84e9920-6777-4981-ab17-b3a5ebb8d0ae
-- title:
--   Lemma 2.4 — a failed attempt gives a sparse cut with $w_C(S, V(C)\setminus S) \le (2/\rho)|S \cap Z_C|$
-- statement:
--   Let $C$ be a piece of the auxiliary graph whose pair vertices have weighted degree at most $1$, let $\rho \ge 128 \log_2(2k)$ be an integer, and let the routing loop from $z_i$ to $z^*$ be at a state with $b_i > 0$ such that no $z_i$-$z^*$ path avoiding the copies of zero capacity has at most $\rho^2$ edges.
--
--   **Lemma 2.4.** There is a set $S \subsetneq V(C)$, a ball $S_h$ around $z_i$ or $z^*$ in $C$ minus those copies with $h \le \rho^2/4$, such that
--   $$0 < |S \cap Z_C| \le \frac{|Z_C|}{2}, \qquad w_C(S, V(C) \setminus S) \le \frac{2}{\rho} |S \cap Z_C|.$$
--
--   This is the step that lets Algorithm 1 recurse: it either routes or cuts cheaply.
--
--   Differences from the source:
--   - generalization: C is a component processed by Algorithm 1 → any piece of the auxiliary graph whose pair vertices have weighted degree ≤ 1; reason: the proof uses only this invariant (p.14), which holds in every processed component
--   - reading: there exists a breadth-first search algorithm that finds S → S has the shape S_h of the proof, with h ≤ ρ²/4; reason: a ball is what breadth-first search finds; running time is carried by the goal
--   - reading: ρ ≥ 128 log(2k), base not printed → 128 log₂(2k) ≤ ρ; reason: base 2 is forced by Lemma 2.5; the floor in h ≤ ρ²/4 still contradicts size k under this bound
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Lemma 2.4, p.13; proof, p.14

import Mathlib
import Definitions.Def_MCPoise_auxGraph
import Definitions.Def_MCPoise_RouteState
import Definitions.Def_MCPoise_IsSparseCut

namespace MCPoise

/-- **Lemma 2.4 (a failed attempt gives a sparse cut).**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Lemma 2.4, p.13: "Let C be a component processed by Algorithm 1, and suppose an attempt to send one unit from z_i to z*_C fails. Then, there
exists a breadth-first search algorithm that finds a set S ⊊ V(C) such that 0 < |S ∩ Z_C| ≤ |Z_C|/2 and w_C(S, V(C) \ S) ≤ (2/ρ)|S ∩ Z_C|."

For a piece `C` of the auxiliary graph whose pair vertices have weighted degree at most `1`, and a loop state `(b, cap, Q)` of Algorithm 1 at `b > 0`
where no path of at most `ρ²` edges avoids the exhausted copies: there is a sparse cut `S`, a ball `S_h` of `C ∖ U` for `U` the exhausted copies.

**Formalization Note.** The failing attempt is stated by its invariant `RouteState`, which is what the proof reads. The weighted-degree bound is the
invariant the proof takes from the initial graph (p.14: "Each pair vertex z_a has weighted degree at most 1 in the initial auxiliary graph, and
deletions only decrease this degree"). Any piece `C` is allowed, not only a component reached by a run. -/
theorem lemma_2_4 {k : ℕ} (lam : Fin k → Fin k → ℝ) (C : (auxGraph lam).Subgraph) (i z : Fin k) (ρ : ℕ)
    (b : ℝ) (cap : Copy k → ℝ) (Q : List (List (AVert k) × ℝ))
    (hw : ∀ a ∈ pairsOf C, wdeg C a ≤ 1)
    (hρ : 128 * Real.logb 2 (2 * (k : ℝ)) ≤ (ρ : ℝ))
    (hz : z ∈ pairsOf C) (hi : i ∈ pairsOf C) (hne : i ≠ z)
    (hst : RouteState ρ C i z b cap Q) (hb : 0 < b) (hfail : RouteFails ρ C i z cap) :
    ∃ S, IsSparseCut ρ C i z (zeroCap cap) S := by sorry

end MCPoise
