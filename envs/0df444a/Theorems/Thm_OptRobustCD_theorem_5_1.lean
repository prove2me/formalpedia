-- Prove2me | Theorems.Thm_OptRobustCD_theorem_5_1
-- name    : OptRobustCD.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:51:55.656006+00:00
-- url     : https://prove2.me/theorems/1c29f724-8a13-414f-9130-dfebae639716
-- title:
--   Theorem 5.1 — robust estimation of the informative nonbacktracking eigenvector in nearly-linear time
-- statement:
--   For every $d\ge1$, $\lambda\in(-1,1)$ with $d\lambda^2>1$, and $\varepsilon>0$ there are $\eta>0$ and a nearly-linear time algorithm with the following guarantee. Let $(G,\sigma^\star)\sim\mathrm{SBM}(n,d,\lambda)$ and let $\xi$ be a unit eigenvector of $B_G$ for its eigenvalue of second-largest modulus. With high probability over $(G,\sigma^\star)$, for every graph $F$ with $|E(F)\triangle E(G)|\le\eta n$, with high probability over its internal randomness the algorithm outputs $\hat\xi(F)$ with
--   $$\min_{a\in\{\pm1\}}\|\hat\xi(F)-a\xi\|\le\varepsilon.$$
--
--   This is the second half of the main theorem: it supplies the initialization of Theorem 4.2 from a corrupted graph.
--
--   Differences from the source:
--   - reading: a nearly-linear time algorithm → one real-RAM program (no oracle) halting within C·N·(log N)^k steps, N = n + |E(F)| + 2, on every graph, encoding and tape; reason: the paper names no machine; worst case is the stronger reading of 'nearly-linear time'
--   - reading: with high probability over (G, σ⋆), for every F, with high probability over the internal randomness → for every δ > 0, for all large n, with SBM-probability ⩾ 1 − δ: for every such ξ, every F within ηn edits and every encoding, the outer tape measure of failure is ⩽ δ; reason: the uniform reading of the nested 'with high probability'
--   - encoding: the output ξ̂(F) ∈ R^{E⃗} → a vector on ordered pairs written as sparse triples (EVecCode); reason: a dense output would take n² steps
--   - reading: let ξ be a unit eigenvector for the eigenvalue of B_G of second-largest modulus → inside the event: such a ξ (IsInfEig) exists, and the conclusion holds for every such ξ; reason: the paper presumes the eigenvalue real and simple, which holds w.h.p.; the existence clause rules out vacuity
-- source:
--   Hopkins, Hua, Mohanty, Rajaraman, Steurer, Optimal Robust Community Detection, STOC 2027 submission (manuscript of November 3, 2026, sha256 3d287d5422db7c4a43e74333bda1dbed204af51a25fd9f2c6e875ae03a4dafa1), Theorem 5.1, p.24 (pdf p.26)

import Mathlib
import Definitions.Def_OptRobustCD_Whp
import Definitions.Def_OptRobustCD_NBMatrix
import Definitions.Def_OptRobustCD_Layouts

namespace OptRobustCD

/-- **Theorem 5.1** (Robust estimation of the informative eigenvector). Hopkins, Hua, Mohanty,
Rajaraman, Steurer, *Optimal Robust Community Detection*, STOC 2027 submission (manuscript of
November 3, 2026, sha256 3d287d54…), Theorem 5.1, p.24 (pdf p.26).

"For every d ⩾ 1, λ ∈ (−1, 1) with dλ² > 1, and ε > 0 there is η > 0 and a nearly-linear time
algorithm with the following guarantee. Let (G, σ⋆) ∼ SBM(n, d, λ) and let ξ be a unit eigenvector
for the eigenvalue of `B_G` of second-largest modulus. With high probability over (G, σ⋆), for
every graph F satisfying |E(F)△E(G)| ⩽ ηn, with high probability over its internal randomness the
algorithm outputs `ξ̂(F)` with `min_{a∈{±1}} ∥ξ̂(F) − aξ∥ ⩽ ε`."

**Formalization Note.**
* The algorithm is one program `P` of the real RAM (`Machine`, no oracle), chosen after
  `d, λ, ε` and before `n`. "Nearly-linear time": on every graph `F` on `[n]`, every encoding and
  every tape it halts within `C·N·(log N)^k` steps, `N = n + |E(F)| + 2`, and outputs a vector on
  ordered pairs (sparse triples, `EVecCode`).
* The nested "with high probability" is uniform: for every `δ > 0`, for all large `n`, with
  SBM-probability at least `1 − δ`, an informative eigenvector exists and for every such `ξ`, every
  `F` within `ηn` edits and every encoding, the tape-probability of failure is at most `δ`
  (outer measure).
* `λ ∈ (−1, 1)`, `d ⩾ 1`, `dλ² > 1` as printed. -/
theorem theorem_5_1 (d lam : ℝ) (hd : 1 ≤ d) (hlam : lam ∈ Set.Ioo (-1 : ℝ) 1)
    (hKS : 1 < d * lam ^ 2) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ P : Program, NoOracle P ∧ ∃ C : ℝ, ∃ k : ℕ,
      (∀ (n : ℕ) (F : SimpleGraph (Fin n)) (c : List ℝ), GraphCode F c →
        HaltsWithin P noOracle c
          (C * ((n : ℝ) + numEdges F + 2) * Real.log ((n : ℝ) + numEdges F + 2) ^ k) ∧
        ∀ ω, ∃ z : EVec n, EVecCode z (finalOut P noOracle c ω)) ∧
      ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
        1 - δ ≤ SBMThreshold.Main.sbmProb n (sbmA d lam) (sbmB d lam) (fun σ G =>
          (∃ ξ : EVec n, IsInfEig G ξ) ∧ ∀ ξ : EVec n, IsInfEig G ξ →
          ∀ F : SimpleGraph (Fin n), (editDist F G : ℝ) ≤ η * n → ∀ c : List ℝ, GraphCode F c →
            tapeMeasure {ω | ¬ ∃ z : EVec n, EVecCode z (finalOut P noOracle c ω) ∧
              min (l2 (z - ξ)) (l2 (z + ξ)) ≤ ε} ≤ ENNReal.ofReal δ) := by sorry

end OptRobustCD
