-- Prove2me | Theorems.Thm_MinSumFPT_lemma_10
-- name    : MinSumFPT.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:18:05.714587+00:00
-- url     : https://prove2.me/theorems/e589a089-c8c4-4d65-8325-457228faf0d2
-- title:
--   Lemma 10 (corrected: $\mathrm{OPT}$ is the target's cost bound) — distance sampling hits the core, conditionally
-- statement:
--   Let $d$ be a pseudometric on $A$ and $\sigma$ a target clustering into $k$ clusters sorted by non-increasing size, and let $\Lambda\ge\mathrm{cost}(\sigma)$. Let $M$ be a nonempty set of points and $0<\varepsilon<1$. Suppose some cluster is not $(\varepsilon,5)$-covered by $M$ (with $\mathrm{OPT}=\Lambda$ in (1)), and let $C_j$ be the one of least index. Then for every $i$ with $\mathrm{core}_2(C_j)\subseteq A_{i,M}$,
--
--   $$
--   P_i\big[p\in\mathrm{core}_2(C_j)\ :\ p\in C_{<j}\cup C_j\big]\ \ge\ \frac{\varepsilon\,\zeta}{k},\qquad \zeta=\frac1{600},
--   $$
--
--   where $C_{<j}=\bigcup_{h<j}C_h$.
--
--   Lemma 10 says that sampling proportionally to the distance from $M$ reaches the core of the largest uncovered cluster with substantial conditional probability. Lemma 11 then removes the conditioning.
--
--   **Formalization Note** The conditional probability is in multiplied form with the weights $d(p,m_p)$.
--
--   Differences from the source:
--   - correction: OPT in (1) is the optimum of the instance, for an arbitrary target clustering (§2.3) → OPT in (1) is any Λ ≥ cost(𝒞) of the target clustering; reason: false otherwise: k = 2, N points each at locations u, v, y with d(u,v) = d(v,y) = D, d(u,y) = h, target C₁ = u ∪ v, C₂ = y, M = {a point at u}: C₁ is (ε,5)-covered, C₂ is not (OPT ≤ 2N²h), A_{0,M} = A, and the conditional probability is h/(D + h) < ε/1200 for h/D small; the proof's (8) uses Σ_h cost(C_h) ≤ OPT, true for Λ ≥ cost(𝒞)
--   - generalization: ∃ a small absolute constant ζ > 0 → ζ = 1/600; reason: the proof fixes ζ ≤ 1/600 (p.16) and Eq. (11) uses ε/(600k); implies the existential
--   - encoding: the probability P_i[X : Y] (resp. P_i[X]) under P_{i,M} → the multiplied form c·w(Y ∩ A_i) ≤ w(X ∩ Y ∩ A_i) with w the weight d(p, m_p); reason: agrees with the ratio when the denominator is positive
--   - encoding: M a set of points (a non-empty node set, p.13) → M a nonempty Finset; reason: m_q needs M ≠ ∅
--   - reading: ε > 0 sufficiently small (ε < 1 definitely suffices) → 0 < ε < 1; reason: the page's own sufficient range
--   - generalization: (A, d) a finite metric space (§2.1, p.7) → every pseudometric d (d(x,x) = 0, d ≥ 0, symmetric, triangle inequality); reason: the goal's input is a semi-metric (footnote 1, p.1); every metric is a pseudometric
-- source:
--   Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), Lemma 10, p.14

import Mathlib
import Definitions.Def_MinSumClust_IsMetric
import Definitions.Def_MinSumFPT_labCost
import Definitions.Def_MinSumFPT_IsCovered
import Definitions.Def_MinSumFPT_wSum
open scoped Classical

namespace MinSumFPT

/-- Lemma 10 (Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, *A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering*, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), Lemma 10, p.14), with ζ = 1/600: let the clusters `C_1, …, C_k` of an
arbitrary target clustering `σ` be sorted by non-increasing size, let `Λ` be at least its cost,
let `M` be a nonempty point set, `0 < ε < 1`, and let `C_j` be the cluster of least index that is
not (ε, 5)-covered by `M`. Then for every `i` with `core₂(C_j) ⊆ A_{i,M}`,
`P_i[p ∈ core₂(C_j) : p ∈ C_{<j} ∪ C_j] ≥ ε ⋅ ζ / k`.

**Formalization Note.** The OPT of (1) is `Λ`, any upper bound on the target's cost (§2.3: "C
denotes an arbitrary target clustering"; see the Differences). The conditional probability is in
multiplied form: `(εζ/k) ⋅ wSum((C_{<j} ∪ C_j) ∩ A_i) ≤ wSum(core₂(C_j) ∩ (C_{<j} ∪ C_j) ∩ A_i)`,
with `C_{<j} ∪ C_j = {x : σ x ≤ j}`. -/
theorem lemma_10 {n k : ℕ} (d : Fin n → Fin n → ℝ) (hd : MinSumClust.IsPseudometric d)
    (σ : Fin n → Fin k)
    (hsort : ∀ i j : Fin k, i ≤ j → (clusterOf σ j).card ≤ (clusterOf σ i).card)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (Λ : ℝ) (hΛ : labCost d σ ≤ Λ)
    (M : Finset (Fin n)) (hM : M.Nonempty) (j : Fin k)
    (hj : ¬ IsCovered d Λ k ε 5 M (clusterOf σ j))
    (hmin : ∀ j' : Fin k, j' < j → IsCovered d Λ k ε 5 M (clusterOf σ j'))
    (i : ℕ) (hi : core d 2 (clusterOf σ j) ⊆ levelSet d M hM i) :
    ε * (1 / 600) / k *
        wSum d M hM (Finset.univ.filter (fun x => σ x ≤ j) ∩ levelSet d M hM i) ≤
      wSum d M hM (core d 2 (clusterOf σ j) ∩ Finset.univ.filter (fun x => σ x ≤ j) ∩
        levelSet d M hM i) := by sorry

end MinSumFPT
