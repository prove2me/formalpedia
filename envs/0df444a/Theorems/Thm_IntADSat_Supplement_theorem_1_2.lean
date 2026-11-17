-- Prove2me | Theorems.Thm_IntADSat_Supplement_theorem_1_2
-- name    : IntADSat.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:55:21.535388+00:00
-- url     : https://prove2.me/theorems/6ed63259-fba5-4cae-97bb-5146c4875095
-- title:
--   Theorem 1.2 (= Corollary C.2) — small-diameter caterpillar identification of $G(n,1/2)$
-- statement:
--   For $n\ge1$ put
--   $$m_n=\Big\lceil 12\sqrt{n\log n}+6\Big\rceil,\qquad \mathcal F_n=\{T:\ T\text{ a caterpillar},\ \operatorname{diam}T\le7,\ |V(T)|\le m_n\},$$
--   including $K_1$, where a caterpillar is a graph isomorphic to some $C(a_0,\dots,a_k)$ and $\log$ is the natural logarithm. Then:
--
--   1. $\mathcal F_n$ has $O(n^3(\log n)^3)$ isomorphism types;
--   2. with probability at least $1-n^{-3/20+o(1)}$, the random graph $G\sim G(n,1/2)$ is determined among all finite simple graphs by $(\hom(T,G))_{T\in\mathcal F_n}$: every finite simple graph $H$ with $\hom(T,H)=\hom(T,G)$ for all $T\in\mathcal F_n$ is isomorphic to $G$.
--
--   The test family is fixed before $G$ is drawn and each test tree has sublinear order; diameter seven suffices for almost every graph, whereas diameter four does not (Proposition C.3).
--
--   **Formalization Note** $G(n,1/2)$ is the uniform law on the labelled simple graphs on $\{0,\dots,n-1\}$, given by the published `erProb` at edge probability $1/2$, as in the mission's goal.
--
--   Differences from the source:
--   - encoding: G ∼ G(n,1/2) → erProb n (1/2), the uniform law on SimpleGraph (Fin n); reason: the published Erdős–Rényi probability used by the base goal; same law
--   - reading: with probability at least 1 − n^{−3/20+o(1)} → ∀ δ > 0, eventually Pr[G not determined by F_n] ≤ n^{−3/20+δ}; reason: the standard reading of an o(1) in the exponent, identical to the base goal theorem_1_1
--   - reading: F_n has O(n³(log n)³) isomorphism types → ∃ C, eventually catTypeCount n ≤ C·n³·(log n)³; reason: definition of O(·) as n → ∞
--   - encoding: every finite simple graph H; T ∈ F_n → H : SimpleGraph (Fin m) for every m; T : SimpleGraph (Fin k) with k ≤ m_n in F_n, isomorphism types as classes modulo ≃g; reason: every finite graph is isomorphic to one on Fin m, and hom counts are isomorphism invariant; m = 0 is never hom-equivalent to G since K₁ ∈ F_n counts vertices
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32826e81e9ed42d927759ebc2d62786404cb2c44cedc931020e3631145), Theorem 1.2, p.2 (PDF 3); restated as Corollary C.2, p.21 (PDF 22)

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting
import Definitions.Def_IntADSat_Supplement_catTypeCount
import Definitions.Def_IntADSat_Supplement_DeterminedByCatFamily

set_option autoImplicit false

namespace IntADSat.Supplement

/-- **Theorem 1.2 (Small-diameter identification; Corollary C.2)** (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), p.2 (PDF 3); Corollary C.2,
p.21 (PDF 22)). Let `F_n` be the family of all ordinary caterpillars with diameter at most seven and at most
`m_n = ⌈12√(n log n) + 6⌉` vertices, including `K_1`. It has `O(n³(log n)³)` isomorphism types. With
probability at least `1 − n^{−3/20+o(1)}`, `G ∼ G(n, 1/2)` is determined among all finite simple graphs by
`(hom(T, G))_{T ∈ F_n}`.

**Formalization Note** `G(n, 1/2)` is the uniform law on `SimpleGraph (Fin n)` (the published `erProb` at
`1/2`, as in the base goal `IntADSat.theorem_1_1`). `O(n³(log n)³)` is read as `∃ C, ∀ᶠ n, count ≤ C n³ (log n)³`;
the failure probability `n^{−3/20+o(1)}` as: for every `δ > 0`, eventually at most `n^{−3/20+δ}`. -/
theorem theorem_1_2 :
    (∃ C : ℝ, ∀ᶠ n : ℕ in Filter.atTop,
      (catTypeCount n : ℝ) ≤ C * (n : ℝ) ^ 3 * Real.log n ^ 3) ∧
    (∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in Filter.atTop,
      LPCommunity.SBMRecovery.erProb n (1 / 2) (fun G => ¬ DeterminedByCatFamily n G) ≤
        (n : ℝ) ^ (-(3 / 20 : ℝ) + δ)) := by sorry

end IntADSat.Supplement
