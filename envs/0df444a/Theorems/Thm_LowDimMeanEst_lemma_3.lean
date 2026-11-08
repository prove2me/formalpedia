-- Prove2me | Theorems.Thm_LowDimMeanEst_lemma_3
-- name    : LowDimMeanEst.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:51:57.239204+00:00
-- url     : https://prove2.me/theorems/58fc9586-8c0c-4dad-8bf2-a9509afa5e96
-- title:
--   Lemma 3 (corrected: α = 0 output when the search fails) — existence of Algorithm 2's output and of a PSD trimming matrix with the KKT maximality property
-- statement:
--   **Lemma 3** (existence of the trimming matrix, and the KKT condition; corrected). Let $x_1,\dots,x_N\in\mathbb R^d$ and $\delta\in(0,1)$. Then:
--
--   1. Algorithm 2 (with correction C1) has an output $w$;
--   2. the printed binary search has an output if and only if at least $\frac13\log\frac1\delta$ of the samples are nonzero;
--   3. for every output $w$ there is a symmetric positive semidefinite **trimming matrix** $A$ with
--   $$w_i=\min(1,\,x_i^\top Ax_i)\qquad(i=1,\dots,N),$$
--   such that for every unit eigenvector $v$ of $A$ with strictly positive eigenvalue and every unit vector $z$, with $\hat\Sigma_{\rm trimmed}=\sum_i(1-w_i)x_ix_i^\top$,
--   $$v^\top\hat\Sigma_{\rm trimmed}v\ \ge\ z^\top\hat\Sigma_{\rm trimmed}z .$$
--
--   In words, the weights trim according to a quadratic form, and the trimmed empirical variance is largest along every direction that was trimmed. This matrix and its maximality property drive the whole analysis of the estimator.
--
--   **Formalization Note** Clause 2 is the content of correction C1: the paper's claim that Algorithm 2 always outputs weights fails when too few samples are nonzero, and the corrected algorithm then returns the solution at $\alpha=0$ (Definition `Algorithm2`).
--
--   Differences from the source:
--   - correction: "Algorithm 2 outputs weights" on every input → Algorithm 2 is the relation IsTrimOutput: the printed search's outputs, or the α = 0 solution when the search has none; reason: if fewer than (1/3)log(1/δ) samples are nonzero the printed search has no output: a zero sample gets weight 0 at every α (all samples 0 under a point mass, a case Theorem 6 allows); the α = 0 solution is the limit of the binary search
--   - encoding: the binary search for α → every solution at every α ∈ [0, α_max] with Σ w_i = (1/3)log(1/δ) is an output; reason: the search's specification; the program's solution is unique at each α
--   - encoding: (1/n′)Σ(1 − w_i)x_ix_i^⊤ ⪯ αI → (1/N)Σ(1 − w_i)⟨x_i, z⟩² ≤ α‖z‖² for all z; reason: the same constraint
--   - encoding: samples indexed by [n′] → Fin N, 0-based; reason: Lean convention
--   - generalization: no claim about when the binary search succeeds → an added clause: the printed search has an output iff at least (1/3)log(1/δ) samples are nonzero; reason: it delimits the inputs on which the correction applies; the other two clauses are the source's (corrected) statement, so the item specializes to it
-- source:
--   Lee, Mathashery, Valiant, Wang, Optimal Sub-Gaussian Mean Estimation in Low Dimensions, STOC 2027 submission (manuscript sha256 7316d30e…), Lemma 3, p.9 (restated p.51, proof pp.52–53)

import Mathlib
import Definitions.Def_LowDimMeanEst_Algorithm2
import Definitions.Def_LowDimMeanEst_TrimmingMatrix

namespace LowDimMeanEst

/-- **Lemma 3** (existence of the trimming matrix, and the KKT condition), p.9 (restated p.51,
proof pp.52–53), with correction C1.

Lee, Mathashery, Valiant, Wang, *Optimal Sub-Gaussian Mean Estimation in Low Dimensions*, STOC 2027
submission (manuscript sha256 7316d30e…).

"For every input sample set x′₁, …, x′_{n′} and parameter δ ∈ (0, 1), Algorithm 2 outputs weights
{wᵢ} such that there exists a symmetric positive semidefinite trimming matrix A satisfying
wᵢ = min(1, x′ᵢ⊤Ax′ᵢ) and the property in the paragraph below: Let v be any unit eigenvector of A
with strictly positive eigenvalue, and consider any other unit vector z ∈ ℝᵈ. Defining the trimmed
empirical covariance Σ̂_trimmed = Σᵢ (1 − wᵢ) x′ᵢx′ᵢ⊤, then it holds that
v⊤Σ̂_trimmed v ≥ z⊤Σ̂_trimmed z."

**Formalization Note.**
* Correction C1: the printed search can have no output (a sample `0` always gets weight `0`, so
  the weight sum never exceeds the number of nonzero samples). The second clause states exactly when
  the printed search succeeds: iff at least `(1/3) log(1/δ)` samples are nonzero. Algorithm 2 is
  the corrected relation `IsTrimOutput`, whose output in the remaining case is the `α = 0` solution.
* The first clause is the existence of an output; the third is the trimming matrix for every output.
-/
theorem lemma_3 {d N : ℕ} (x : Fin N → E d) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (∃ w : Fin N → ℝ, IsTrimOutput x δ w) ∧
      ((∃ w : Fin N → ℝ, IsSearchOutput x δ w) ↔
        logInv δ / 3 ≤ ((Finset.univ.filter (fun i => x i ≠ 0)).card : ℝ)) ∧
      ∀ w : Fin N → ℝ, IsTrimOutput x δ w → ∃ A : E d →L[ℝ] E d, IsKKTMatrix x w A := by sorry

end LowDimMeanEst
