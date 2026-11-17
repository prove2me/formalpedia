-- Prove2me | Theorems.Thm_ImpatientMatching_Supplement_theorem_3_1
-- name    : ImpatientMatching.Supplement.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:31:01.722244+00:00
-- url     : https://prove2.me/theorems/67401651-bc9e-4186-8cf5-eb4d12f0600f
-- title:
--   Theorem 3.1 — infinite patience on a vertex cover
-- statement:
--   Let $G=(S,C,E_G)$ be a finite bipartite compatibility graph. Supplier type $i$ and customer type $j$ arrive as independent Poisson processes with positive rational rates $\lambda_i$ and $\gamma_j$. Compatible edge $(i,j)$ has nonnegative rational reward $w_{ij}$, and finite positive abandonment rates are rational. Suppose every compatibility edge has at least one infinitely patient endpoint; the chosen side may vary from edge to edge.
--
--   Let
--
--   $$
--   F^*=\max\left\{\sum_{(i,j)\in E_G}w_{ij}f_{ij}:
--   f_{ij}\ge0,\ \sum_j f_{ij}\le\lambda_i,\ \sum_i f_{ij}\le\gamma_j\right\}.
--   $$
--
--   Then the optimal long-run average reward equals the weighted-flow optimum:
--
--   $$
--   g^*=F^*.
--   $$
--
--   Moreover, one uniform polynomial-time algorithm computes a polynomial-length rational description of an optimal flow $f$, one infinitely patient storage endpoint for each positive-flow edge, and the associated per-edge routing policy $\pi$. This policy is admissible, attains $g^*$ exactly, and for every $T>0$ satisfies
--
--   $$
--   0\le F^*-r^\pi(T)
--   \le 2\sqrt{\frac{2}{T}}
--     \sum_{(i,j)\in E_G}w_{ij}\sqrt{f_{ij}}.
--   $$
--
--   The result covers the Infinite-Infinite, Infinite-Finite and Infinite-Zero regimes and, more generally, edgewise mixtures of patient endpoints.
--
--   **Formalization Note** The algorithm is quantified before the input, so its code cannot depend on the instance. Its output is the rational flow and storage-endpoint description; the Lean definition deterministically realizes the policy by independent categorical routing and a separate FIFO inventory on every edge. The finite-horizon inequality is stated in $[0,\infty]$ as $r^\pi(T)\le F^*$ together with the displayed difference bound, which is equivalent to the real inequality and avoids truncated-subtraction ambiguity.
--
--   Differences from the source:
--   - encoding: finite sets $S,C$, independent Poisson streams and patience parameters in $[0,\infty]$ → the blocks `Fin nS`, `Fin nC`, the published superposed marked-Poisson seed space, and explicit infinite/positive-rational-exponential/immediate lifetime constructors; reason: these encode the same finite rational instances, and the superposed marked process has the law of the independent streams
--   - encoding: nonnegative real rewards, expectations, $r^\pi$, $g^\pi$ and $g^*$ → $[0,\infty]$ values and lower Lebesgue integrals; reason: all rewards are nonnegative and the theorem's finite bound excludes infinity, while the representation has no nonintegrability default value
--   - encoding: $0\le F^*-r^\pi(T)$ in ordinary real arithmetic → $r^\pi(T)\le F^*$ together with the corresponding truncated $[0,\infty]$ difference; reason: the explicit order guard makes the extended-nonnegative statement equivalent to the source inequality and prevents truncation from hiding an oversized rate
--   - encoding: the real flow LP and its polynomial-time rational solution → $F^*$ is the supremum of feasible real flow values and the computed policy description contains a rational feasible flow attaining it; reason: the source assumes rational input and Appendix A explicitly states that linear programming returns an optimal flow of polynomial encoding length
--   - encoding: a policy that can be described and computed in polynomial time → one Cook-machine computable binary-string function, quantified before all inputs, plus one uniform polynomial bound on its output length; reason: this is the source's binary-input computational clause made explicit
--   - encoding: storage choices only on positive-flow edges and an unspecified stored agent when several are available → a total storage-choice table whose zero-flow entries are ignored and FIFO tie-breaking within each edge inventory; reason: this fixes a finite canonical encoding and one concrete witness without changing routing probabilities, rewards, or any source instance
--   - encoding: observed history contains only real arrivals and abandonments → the filtration also reveals the later virtual departure time of an already matched finite-patience agent; reason: that unused patience time is independent of the future and supplies only extra private randomization, the upper bound holds for this broader class, and the constructed policy does not use it
-- source:
--   C. Yan and S. M. Varma, Impatience Makes Matching NP-Hard, manuscript (sha256 7b1051b6c661435675185b0663cb08ab217698a2c4ee07fa0f473686dbb6bed9), Theorem 3.1 and displays (2)–(3), p.8; proof and policy construction, Appendix A, pp.24–25

import Definitions.Def_ImpatientMatching_Supplement_PatientModel

open scoped ENNReal

namespace ImpatientMatching.Supplement

/-- **Theorem 3.1 (Infinite patience on a vertex cover).** Yan–Varma, manuscript
(sha256 7b1051b6…), §3.1, p.8; policy construction and proof in Appendix A, pp.24–25.

For every rational weighted bipartite matching input in which each compatibility edge has at least
one infinitely patient endpoint, the optimal long-run reward `g*` equals the weighted-flow optimum
`F*`. One uniform polynomial-time algorithm returns a polynomial-length rational optimal-flow and
per-edge-storage description. Its canonical policy attains `g*` exactly and, for every `T > 0`,
satisfies the full bound (3).

**Formalization Note.** The algorithm is quantified before the input, so it cannot depend on the
instance. The flow LP is over real flows; its encoded optimum is rational, as Appendix A states for
rational data. Rewards and expected rewards live in `ℝ≥0∞`; the explicit upper bound makes all
quantities finite and avoids real-supremum or nonintegrable-expectation default values. -/
theorem theorem_3_1 :
    ∃ (build : List Bool → List Bool) (degree : ℕ),
      CookPvsNP.PolyTimeComputable build ∧
      ∀ I : PatientInput, PatientEdgeCover I →
        patientGStar I = ENNReal.ofReal (FStar I) ∧
        ∃ d : PolicyDescription I,
          build (encPatientInput I) = encPolicyDescription d ∧
          (encPolicyDescription d).length ≤ (encPatientInput I).length ^ degree + degree ∧
          IsPatientPolicy I (storageRoutingPolicy I d) ∧
          patientLongRunReward I (storageRoutingPolicy I d) = patientGStar I ∧
          ∀ T : ℝ, 0 < T →
            patientRate I (storageRoutingPolicy I d) T ≤ ENNReal.ofReal (FStar I) ∧
            ENNReal.ofReal (FStar I) - patientRate I (storageRoutingPolicy I d) T ≤
              ENNReal.ofReal
                (2 * Real.sqrt (2 / T) *
                  ∑ i, ∑ j, (I.reward i j : ℝ) * Real.sqrt (d.flow i j : ℝ)) := by sorry

end ImpatientMatching.Supplement
