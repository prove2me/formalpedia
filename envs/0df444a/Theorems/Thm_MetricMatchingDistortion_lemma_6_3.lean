-- Prove2me | Theorems.Thm_MetricMatchingDistortion_lemma_6_3
-- name    : MetricMatchingDistortion.lemma_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:21:06.801732+00:00
-- url     : https://prove2.me/theorems/120a558d-519d-4169-be2f-a5d933166fa3
-- title:
--   Lemma 6.3 — the flow matrix $F(t)$ costs at most $\mathrm{cost}(M^*)+\mathrm{cost}(X(t))$
-- statement:
--   For every $n\ge1$, every ranking profile, every pseudometric $d$ consistent with it, every perfect matching $\pi^*$ and every $t\in[0,1)$, let $f$ be the flow in which each item $b$ sends $X_{a,b}(t)$ to agent $a$ and each agent $a$ sends $1$ to $\pi^*(a)$. Then $f$ has a decomposition $f=\sum_P\alpha_P\mathbf 1_P+\sum_Q\beta_Q\mathbf 1_Q$ into agent-to-item paths and cycles with nonnegative weights, and for **every** such decomposition the matrix $F(t)$, $F_{ab}(t)=\sum_{P\text{ from }a\text{ to }b}\alpha_P$, has row sums $1-t$, column sums $q_b(t)$, and
--   $$\mathrm{cost}(F(t),d)\le\mathrm{cost}(\pi^*,d)+\mathrm{cost}(X(t),d).$$
--
--   It is the comparison matrix behind the rate inequality of Lemma 6.4.
--
--   Differences from the source:
--   - generalization: F(t) from the decomposition the flow decomposition theorem provides, into simple paths and cycles → F(t) from every decomposition into walks and closed walks, together with the existence of one; reason: the page's decomposition is one of these, so the statement specializes to the page's F(t)
--   - generalization: Lemma 6.3 states the cost bound; the row and column sums are the "Note that" sentence before it (p.52) → both in the conclusion; reason: the page records them for the same F(t); the cost bound is the page's lemma
--   - encoding: OPT = cost(M*, d) for an optimal matching M* → cost(π*, d) for every perfect matching π*; reason: OPT is the minimum over perfect matchings and the coefficient is nonnegative, so the two bounds are equivalent
--   - encoding: X(t) = PS run for t units of time (Algorithm 7) → psAlloc: the eating step ExAnteExPost.RPS.eatStep with favorite-available-item picks, iterated n+1 times from capacities 1, the zero matrix and time budget t; reason: every step but the last exhausts an item, so n+1 steps run PS to time t
--   - encoding: n ≥ 1 (standing, §2 p.9) → [NeZero n]; reason: the same condition as a type class
-- source:
--   Charikar, Haqi, Hastings, Huang, Ramakrishnan, Sublinear Metric Distortion for Matching, arXiv:2611.05777 (held version, sha256 fdf3452b105082d6ff680c8a762ec950298417efdebeb216b721705a9802e0da), Lemma 6.3, p.52 (PDF p.54); construction of F(t), pp.51–52

import Mathlib
import Definitions.Def_MetricMatchingDistortion_IsConsistentPseudometric
import Definitions.Def_MetricMatchingDistortion_matchingCost
import Definitions.Def_MetricMatchingDistortion_IsPartialFractionalMatching
import Definitions.Def_MetricMatchingDistortion_psAlloc
import Definitions.Def_MetricMatchingDistortion_IsFlowDecomp

namespace MetricMatchingDistortion

/-- **Lemma 6.3.** Charikar et al., *Sublinear Metric Distortion for Matching*, arXiv:2611.05777 (held version,
sha256 fdf3452b…), Lemma 6.3, p.52 (PDF p.54): "For every time t ∈ [0, 1), the matrix F(t) satisfies cost(F(t), d) ≤ cost(M∗, d) +
cost(X(t), d)." The matrix F(t) is built on pp.51–52 from a decomposition f = ∑_P α_P 1_P + ∑_Q β_Q 1_Q
of the flow f (each item b sends X_{a,b}(t) to agent a, each agent a sends 1 to M∗(a); `psFlow`) into
agent-to-item paths and cycles, F_{ab}(t) = ∑_{P∈𝒫_{ab}} α_P (`pathMatrix`): "Note that the resulting
matrix F(t) = (F_{ab}(t)) has row sums 1 − t and column sums q_b(t)".

For `t ∈ [0, 1)`, every consistent pseudometric `d` and every perfect matching `π*`: the flow `f`
has a path–cycle decomposition, and for **every** such decomposition the matrix `F(t)` it defines
has row sums `1 − t`, column sums `q_b(t)` and cost at most `cost(π*, d) + cost(X(t), d)`.

**Formalization Note.** The page fixes one decomposition given by the flow decomposition theorem;
the lemma is stated for every decomposition (into walks, see `IsFlowDecomp`), and the existence
of one is the first clause. The row and column sums are the page's "Note that" sentence before the
lemma. `M∗` may be any perfect matching. -/
theorem lemma_6_3 (n : ℕ) [NeZero n] (rk : Ranking n) (d : Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ)
    (hd : IsConsistentPseudometric rk d) (πstar : Equiv.Perm (Fin n)) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : t < 1) :
    (∃ paths cycles, IsFlowDecomp (psFlow (psAlloc rk t) πstar) paths cycles) ∧
      ∀ paths cycles, IsFlowDecomp (psFlow (psAlloc rk t) πstar) paths cycles →
        (∀ a, ∑ b, pathMatrix paths a b = 1 - t) ∧
          (∀ b, ∑ a, pathMatrix paths a b = remaining rk t b) ∧
          fracCost (pathMatrix paths) d ≤ matchingCost πstar d + fracCost (psAlloc rk t) d := by sorry

end MetricMatchingDistortion
