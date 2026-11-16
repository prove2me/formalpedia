-- Prove2me | Theorems.Thm_LogConcaveLattice_Lift_Supplement_theorem_1_2
-- name    : LogConcaveLattice.Lift.Supplement.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:34:47.618431+00:00
-- url     : https://prove2.me/theorems/8464643d-09ff-4d2c-a56b-2b5918cca480
-- title:
--   Theorem 1.2 — covering radius bound $\mu(\Lambda,K)\le\sqrt{2e/\pi}\,\mathbb E\|G\|_K$ when $\Lambda^*$ is weakly stable
-- statement:
--   Let $\Lambda\subseteq\mathbb R^n$ be a full-rank lattice whose dual lattice $\Lambda^*=\{y:\langle y,\lambda\rangle\in\mathbb Z\ \forall\lambda\in\Lambda\}$ is weakly stable, i.e. every sublattice $\Gamma\subseteq\Lambda^*$ (of any rank) has $\det\Gamma\ge1$. Let $K\subseteq\mathbb R^n$ be a convex body (a compact convex set) with $0\in\operatorname{int}(K)$, with Minkowski functional $\|x\|_K=\inf\{r>0:x\in rK\}$, and let $G\sim N(0,\mathrm{Id})$ be a standard Gaussian random vector in $\mathbb R^n$. Then the covering radius $\mu(\Lambda,K)=\min\{r\ge0:\Lambda+rK=\mathbb R^n\}$ satisfies
--
--   $$\mu(\Lambda,K)\ \le\ \sqrt{\frac{2e}{\pi}}\cdot\mathbb E\,\|G\|_K .$$
--
--   $K$ need not be symmetric and $\det\Lambda$ is not normalized. This is the paper's first application of the log-concave lattice lift (Theorem 1.1); it yields the subspace-flatness bound $C_{KL}(n)=O(\log^{3/2}n)$ and the flatness bound $\mathrm{Flt}(n)=O(n\sqrt{\log n})$ (Corollaries 1.3, 1.4).
--
--   **Formalization Note** The lattice is a discrete full-rank $\mathbb Z$-submodule of `EuclideanSpace ℝ (Fin n)` (`IsZLattice`); weak stability and the dual are the mission's published definitions. The restatement on p. 15 says only "lattice"; by the standing convention of §2.3 (p. 7) and the statement on p. 4 it is full rank. The covering radius is the supplement's definition `coveringRadius` (an `sInf` that is attained under these hypotheses), $\|\cdot\|_K$ is `gauge K` and $G$ has law `stdGaussian (V n)`; integrability of $\|\cdot\|_K$ against the Gaussian is part of the conclusion, so the right-hand side is the true expectation and not the Bochner junk value $0$.
--
--   Differences from the source:
--   - encoding: K ⊆ ℝⁿ a convex body with 0 ∈ int(K) → K convex and compact with 0 ∈ interior K; reason: a convex body is a compact convex set with nonempty interior, and nonempty interior is implied by 0 ∈ int(K); same instances
--   - encoding: E ‖G‖_K with G ∼ N(0, Id) → ∫ gauge K x ∂(stdGaussian (V n)), the Bochner integral of the Minkowski functional against Mathlib's standard Gaussian measure on EuclideanSpace ℝ (Fin n), with integrability of gauge K against it asserted; reason: stdGaussian is the law N(0, Id); gauge K is continuous and grows linearly for 0 ∈ int K, so the asserted integrability holds in every instance and the integral is the true expectation; the clause guards against the Bochner junk value 0
--   - encoding: µ(Λ, K) = min{r ≥ 0 : Λ + rK = ℝⁿ} → coveringRadius Λ K = sInf {r ≥ 0 : ∀ x, ∃ λ ∈ Λ, ∃ k ∈ K, x = λ + r k}; reason: under the hypotheses the set is nonempty, closed and bounded below by 0, so the infimum is the minimum
-- source:
--   Letwin, Reis, Rothvoss, Strongly Log-Concave Measures and Lattices, STOC 2027 submission #401 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/401.pdf, SHA-256 c2ca89e66a6221772830cc9470a9d1f7fb2afeb8fc716a1b283f35b2280c5eac, Theorem 1.2, p. 4 (restated as "Theorem (Theorem 1.2)" and proved on p. 15); covering radius and Minkowski functional p. 4; weak stability p. 2; dual lattice p. 1; full rank by default §2.3 p. 7

import Mathlib
import Definitions.Def_LogConcaveLattice_Lift_Lattice
import Definitions.Def_LogConcaveLattice_Lift_Supplement_CoveringRadius

open MeasureTheory ProbabilityTheory

namespace LogConcaveLattice.Lift.Supplement

/-- **Theorem 1.2** (covering radius bound; Letwin–Reis–Rothvoss, p. 4, restated and proved
p. 15). Let `Λ ⊆ ℝⁿ` be a full-rank lattice whose dual `Λ*` is weakly stable and let `K ⊆ ℝⁿ`
be a convex body (compact, convex) with `0 ∈ int K`. Then
`µ(Λ, K) ≤ √(2e/π) · E ‖G‖_K` with `G ∼ N(0, Id)` standard Gaussian and `‖·‖_K = gauge K`.
`K` need not be symmetric; the expectation `E ‖G‖_K` is asserted to exist. -/
theorem theorem_1_2 (n : ℕ) (Λ : Submodule ℤ (V n)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hΛ : WeaklyStable (dual Λ)) (K : Set (V n)) (hKconv : Convex ℝ K) (hKcpt : IsCompact K)
    (hK0 : (0 : V n) ∈ interior K) :
    Integrable (fun x => gauge K x) (stdGaussian (V n)) ∧
      coveringRadius Λ K ≤
        Real.sqrt (2 * Real.exp 1 / Real.pi) * ∫ x, gauge K x ∂(stdGaussian (V n)) := by sorry

end LogConcaveLattice.Lift.Supplement
