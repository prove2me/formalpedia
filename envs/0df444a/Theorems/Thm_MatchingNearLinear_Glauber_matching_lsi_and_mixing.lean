-- Prove2me | Theorems.Thm_MatchingNearLinear_Glauber_matching_lsi_and_mixing
-- name    : MatchingNearLinear.Glauber.matching_lsi_and_mixing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T15:57:40.528221+00:00
-- url     : https://prove2.me/theorems/ca2d2fcf-86e4-4146-9216-aa1157e5a99f
-- title:
--   Corollary 4.3 — Log-Sobolev inequalities and mixing for matchings
-- statement:
--   There is a universal constant $c>0$. Let $G$ have $n$ vertices and $m\ge1$ edges with $0<\lambda_e\le a$, $a>0$. Write $\Delta$ for its maximum degree, $\lambda_{\min}=\min_e\lambda_e$, $p=\mu_{G,\lambda}$ and $p_{\min}=\min_Mp(M)$. Let $c_a=e^{-I_a}$ as in Eq. (20), and put
--
--   $$L=\log\left(1+\frac{m(1+a)(1+a\Delta)^2}{\lambda_{\min}}\right),\qquad B=cm(1+a)c_a^{-1}.$$
--
--   Then $\alpha_{\rm LS}^{-1},\alpha_{\rm mLS}^{-1}\le BL$, and for every $0<\varepsilon\le1/2$,
--
--   $$t_{\rm mix}(\varepsilon)\le B\left[L\log\log(e^2/p_{\min})+\log(1/\varepsilon)\right].$$
--
--   After every feasible edge pin, the residual conditional law equals the matching law of the inherited residual graph, and the same estimates apply whenever that graph has at least one edge, counting one residual-edge update per step. For fixed $a,d>0$ and $\lambda_{\min}\ge n^{-d}$, the inverse constants are $O_{a,d}(m\log n)$ and mixing is $O_{a,d}(m[\log^2n+\log(1/\varepsilon)])$. At any fixed uniform activity $\lambda_e=a>0$ these bounds have constants depending only on $a$, without a minimum-activity promise. This retains the separate spectral-gap accuracy term used in the goal.
--
--   Differences from the source:
--   - encoding: finite simple graphs with labeled edge lists → vertices Fin n and edges Fin m with distinct endpoints and injective unordered endpoint map; reason: every finite source graph admits this encoding, including isolated vertices and disconnected graphs
--   - encoding: an upper bound on the inverse optimal log-Sobolev or modified log-Sobolev constant → the corresponding functional inequality with the asserted coefficient; reason: these are equivalent for the source irreducible finite kernels and avoid default values for invalid extrema
--   - encoding: least nonnegative integer worst-start mixing time bounded by B → existence of a natural horizon t with t ≤ B and total-variation error at most epsilon from every starting state; reason: this is equivalent to the least-time bound and certifies a nonempty set of mixing times
--   - encoding: parameter-uniform or universal big-O bounds → a positive existential constant before all instance parameters; secondary asymptotic clauses quantify fixed bounds first; reason: this is the precise uniform meaning of the source asymptotic notation
--   - encoding: residual matching laws after feasible pins → explicit push-forward to a bijectively labeled residual edge list, keeping deleted vertices as isolated labels; reason: the matching law and residual-edge update clock are unchanged
-- source:
--   Tianshun Miao, Yitong Yin, Sampling Matchings in Near-linear Time, STOC 2027 submission #444 (October 2026), Corollary 4.3, printed p. 20 (PDF p. 22); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/444.pdf

import Mathlib
import Definitions.Def_MatchingNearLinear_Glauber_CovarianceRate

set_option autoImplicit false

namespace MatchingNearLinear.Glauber

/-- Tianshun Miao and Yitong Yin, Sampling Matchings in Near-linear Time,
STOC 2027 submission #444 (October 2026). Exact result and pages in the item metadata. -/

theorem matching_lsi_and_mixing :
    (∃ c : ℝ, 0 < c ∧ ∀ (n m : ℕ), 1 ≤ m → ∀ (G : Input n m) (a : ℝ), 0 < a →
      ∀ lam : Fin m → ℝ, ActivityBound lam a →
      let p := matchingLaw G lam
      let B := c*m*(1+a)/(matchingC a)
      LSIBound (supportMass p) (subsetGlauber p) (B*matchingLogFactor G lam a) ∧
      MLSIBound (supportMass p) (subsetGlauber p) (B*matchingLogFactor G lam a) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 → MixingBound (supportMass p) (subsetGlauber p) ε
        (B*(matchingLogFactor G lam a * Real.log (Real.log (Real.exp 2/minMass (supportMass p))) +
          Real.log (1/ε))) ∧
      (∀ τ : Fin m → Option Bool, 0 < eventMass p indicator τ →
        let H := residualInput G τ
        let rlam := residualActivities G τ lam
        let q := matchingLaw H rlam
        (∀ S, residualPushLaw G lam τ S = q S) ∧
        (1 ≤ residualEdgeCount G τ →
          let Br := c * residualEdgeCount G τ * (1+a) / matchingC a
          LSIBound (supportMass q) (subsetGlauber q) (Br*matchingLogFactor H rlam a) ∧
          MLSIBound (supportMass q) (subsetGlauber q) (Br*matchingLogFactor H rlam a) ∧
          ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 → MixingBound (supportMass q) (subsetGlauber q) ε
            (Br*(matchingLogFactor H rlam a * Real.log (Real.log (Real.exp 2/minMass (supportMass q))) +
              Real.log (1/ε)))))) ∧
    (∀ a d : ℝ, 0 < a → 0 < d → ∃ c : ℝ, 0 < c ∧
      ∀ (n m : ℕ), 1 ≤ m → ∀ (G : Input n m) (lam : Fin m → ℝ),
      ActivityBound lam a → (n:ℝ)^(-d) ≤ minActivity lam →
      let p := matchingLaw G lam
      LSIBound (supportMass p) (subsetGlauber p) (c*m*Real.log n) ∧
      MLSIBound (supportMass p) (subsetGlauber p) (c*m*Real.log n) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 → MixingBound (supportMass p) (subsetGlauber p) ε
        (c*m*((Real.log n)^2+Real.log (1/ε)))) ∧
    (∀ a : ℝ, 0 < a → ∃ c : ℝ, 0 < c ∧ ∀ (n m : ℕ), 1 ≤ m → ∀ G : Input n m,
      let p := matchingLaw G (fun _ => a)
      LSIBound (supportMass p) (subsetGlauber p) (c*m*Real.log n) ∧
      MLSIBound (supportMass p) (subsetGlauber p) (c*m*Real.log n) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 → MixingBound (supportMass p) (subsetGlauber p) ε
        (c*m*((Real.log n)^2+Real.log (1/ε)))) := by sorry

end MatchingNearLinear.Glauber
