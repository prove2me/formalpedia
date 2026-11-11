-- Prove2me | Theorems.Thm_MatchingNearLinear_Glauber_monomer_covariance_row_sums
-- name    : MatchingNearLinear.Glauber.monomer_covariance_row_sums
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T15:56:37.003289+00:00
-- url     : https://prove2.me/theorems/6865b06f-6f94-43db-b0f3-a873bfacadc4
-- title:
--   Lemma A.3 — Monomer covariance and absolute row sums
-- statement:
--   Let $G$ be any finite simple graph with arbitrary positive edge activities $\lambda_e$ and positive monomer weights $z_v$. Give each matching mass proportional to $\prod_{e\in M}\lambda_e\prod_{v:J_v(M)=1}z_v$, where $J_v$ indicates that $v$ is unmatched. Condition on any feasible specification $\tau$ of present or absent monomer indicators, and put $q_v=E_{p^\tau}J_v$. Then
--
--   $$\operatorname{Cov}_{p^\tau}(J)\preceq2\operatorname{Diag}(q),$$
--
--   and for every vertex $v$,
--
--   $$\sum_{w\ne v}|\operatorname{Cov}(J_v,J_w)|\le q_v(1-q_v),\qquad \sum_w|\operatorname{Cov}(J_v,J_w)|\le2q_v(1-q_v)\le2q_v.$$
--
--   All covariances are conditional ones. The spectral inequality and both row-sum assertions are separate conclusions, including deterministic coordinates and edgeless graphs. This supplies the weighted monomer input to the edge covariance estimate.
--
--   Differences from the source:
--   - encoding: finite simple graphs with labeled edge lists → vertices Fin n and edges Fin m with distinct endpoints and injective unordered endpoint map; reason: every finite source graph admits this encoding, including isolated vertices and disconnected graphs
-- source:
--   Tianshun Miao, Yitong Yin, Sampling Matchings in Near-linear Time, STOC 2027 submission #444 (October 2026), Lemma A.3, printed p. 48 (PDF p. 50); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/444.pdf

import Mathlib
import Definitions.Def_MatchingNearLinear_Glauber_MatchingModel

set_option autoImplicit false

namespace MatchingNearLinear.Glauber

/-- Tianshun Miao and Yitong Yin, Sampling Matchings in Near-linear Time,
STOC 2027 submission #444 (October 2026). Exact result and pages in the item metadata. -/

theorem monomer_covariance_row_sums
    (n m : ℕ) (G : Input n m) (lam : Fin m → ℝ) (z : Fin n → ℝ)
    (hlam : ∀ e, 0 < lam e) (hz : ∀ v, 0 < z v)
    (τ : Fin n → Option Bool)
    (hτ : 0 < eventMass (monomerWeightedLaw G lam z) (monomer G) τ) :
    let q := conditionObservables (monomerWeightedLaw G lam z) (monomer G) τ
    ObservableCovarianceBound q (monomer G) 2 ∧
    ∀ v : Fin n,
      (∑ w ∈ Finset.univ.erase v, |observableCov q (monomer G) v w|) ≤
        observableMean q (monomer G) v * (1-observableMean q (monomer G) v) ∧
      (∑ w, |observableCov q (monomer G) v w|) ≤
        2*observableMean q (monomer G) v * (1-observableMean q (monomer G) v) ∧
      2*observableMean q (monomer G) v * (1-observableMean q (monomer G) v) ≤
        2*observableMean q (monomer G) v := by sorry

end MatchingNearLinear.Glauber
