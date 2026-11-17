-- Prove2me | Theorems.Thm_LloydConvergence_lloyd_converges
-- name    : LloydConvergence.lloyd_converges
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-17T05:08:05.757304+00:00
-- url     : https://prove2.me/theorems/20b96a8d-1366-405e-9a95-82700ac76aa2
-- title:
--   Lloyd's algorithm converges in finitely many steps to a fixed point
-- statement:
--   Lloyd's algorithm for $k$-means clustering converges in finitely many steps to a fixed point.
--
--   Let $S$ be a finite set of points in $\mathbb{R}^n$ and $k \geq 1$. An assignment $f : S \to \{1, \dots, k\}$ has centers $\mu_i$, the mean of the points assigned to cluster $i$ (with $\mu_i = 0$ if cluster $i$ is empty). One Lloyd step reassigns each point to its nearest center — but only when that center is strictly nearer than its current one (strict-move tie-breaking; on ties the point stays put). Then there is a number of steps $T \leq k^{|S|}$ such that the $T$-fold iterate of the step is a fixed point: every point is already at a nearest centroid, and every centroid is the mean of its cluster.
--
--   In other words, the iteration cannot cycle: the $k$-means objective strictly decreases at every step that changes the assignment, and there are only $k^{|S|}$ assignments. The fixed point is a local minimum in the sense of Lloyd's algorithm — a stable assignment with optimal centers — not a global optimum of the $k$-means objective.
--
--   **Formalization Note** The iteration is the one defined in the platform definition `LloydConvergence` (strict-move step, empty-cluster centroid $0$); the partition in the statement is `LloydConvergence.part` and the iterate is `LloydConvergence.orbit`.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, Section 22.2, pp. 312-313 (k-means algorithm and Lemma 22.1); Lloyd, Least squares quantization in PCM, IEEE Trans. Inform. Theory 28 (1982)

import Mathlib
import Definitions.Def_UnderstandingML_Clustering
import Definitions.Def_LloydConvergence

theorem LloydConvergence.lloyd_converges {n k : ℕ} (S : Finset (UnderstandingML.Vec n)) [NeZero k]
    (f₀ : S → Fin k) :
    ∃ T : ℕ, T ≤ k ^ S.card ∧
      (∀ x : S, ∀ j : Fin k,
        ‖(x : UnderstandingML.Vec n)
          - UnderstandingML.centroid (LloydConvergence.part S (LloydConvergence.orbit S f₀ T) ((LloydConvergence.orbit S f₀ T) x))‖
          ≤ ‖(x : UnderstandingML.Vec n)
            - UnderstandingML.centroid (LloydConvergence.part S (LloydConvergence.orbit S f₀ T) j)‖) := by sorry
