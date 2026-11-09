-- Prove2me | Theorems.Thm_MemOracleLB_Optimization_lemma_4_1
-- name    : MemOracleLB.Optimization.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:35:52.61397+00:00
-- url     : https://prove2.me/theorems/a88ca461-1fa9-4fcd-ba60-2e3a059728e7
-- title:
--   Lemma 4.1 — Good event and radius bounds
-- statement:
--   There exists an absolute $C_0\ge2$ such that, for every fixed $\ell\ge1$, there are $C>0$ and a dimension threshold with the following properties. Set $n=m+1$, $L=\ell n$, draw all entries of $R$ independently from $N(0,1/n)$, and put $s=R^{-1}e_n$. Define
--
--   $$\mathcal H=\{\max_i\|R_i\|\le2,\ \|R^{-1}\|_{\rm op}\le C_0n,\ \sqrt n/C_0\le\|s\|\le C_0\sqrt n\}.$$
--
--   For every sufficiently large $n$,
--
--   $$\Pr(\mathcal H^c)\le2^{-14},\qquad B^n\subseteq2K_j(R)\subseteq Cn^{3/2}B^n\quad(R\in\mathcal H,\ j=1,2).$$
--
--   The constant $C$ may depend only on the fixed multiple $\ell$, and $C_0$ is uniform even over that multiple. Both bodies and both radius inclusions are retained.
--
--   Differences from the source:
--   - encoding: real Euclidean spaces, independent rows and Gaussian relative entropy → EuclideanSpace with Fin indices, product measures and Mathlib klDiv in [0,infinity]; reason: the same spaces, independent laws and divergence values, including infinite entropy
--   - encoding: n-1 rows in n dimensions → m rows in dimension m+1; reason: renaming n=m+1 avoids truncated natural subtraction and changes no positive-dimensional instance
--   - encoding: the standing sufficiently large absolute ambient dimension on PDF p.8 → an existential natural threshold N at least 2 before the dimension and all instance data; reason: this makes the source asymptotic quantifier explicit and keeps logarithms and denominators in their stated domains
--   - generalization: L is a fixed sufficiently large universal multiple of n → every fixed L=ell*n with ell>=1, with radius constant C allowed to depend on ell; reason: the source proof gives the inclusions for all these multiples and its chosen multiple is included
--   - encoding: j=1,2 and the dilated bodies 2K_j → b=1,3 in the last constraint and the image of K_b under x maps to 2*x; reason: these are exactly the two source bodies and their scalar dilations
-- source:
--   Santosh Vempala, STOC 2027 submission #365 (October 2026), Lemma 4.1, PDF p. 19 (printed p. 18), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/365.pdf

import Mathlib
import Definitions.Def_MemOracleLB_Optimization_OracleModel

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

namespace MemOracleLB.Optimization

/-- Lemma 4.1, PDF p.19 (printed p.18). Both bodies and both inclusions in (9).
The radius constant may depend on the fixed multiple ell, never on dimension. -/
theorem lemma_4_1 : ∃ C₀ : ℝ, 2 ≤ C₀ ∧
    ∀ ℓ : ℝ, 1 ≤ ℓ → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧
      ∀ m : ℕ, N ≤ m + 1 →
        matrixLaw (m + 1) (GoodEvent (m := m) C₀)ᶜ ≤ (2 : ℝ≥0∞) ^ (-14 : ℤ) ∧
        ∀ R ∈ GoodEvent (m := m) C₀, ∀ b ∈ ({1, 3} : Set ℝ),
          Metric.closedBall (0 : E (m + 1)) 1 ⊆
            (fun x => (2 : ℝ) • x) '' hardBody R (ℓ * (m + 1)) b ∧
          (fun x => (2 : ℝ) • x) '' hardBody R (ℓ * (m + 1)) b ⊆
            Metric.closedBall 0 (C * (m + 1 : ℝ) ^ (3 / 2 : ℝ)) := by sorry

end MemOracleLB.Optimization
