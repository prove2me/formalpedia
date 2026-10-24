-- Prove2me | Theorems.Thm_OAI_SharpLiebThirring_ActionProof_matrix_compact_penalty
-- name    : OAI.SharpLiebThirring.ActionProof.matrix_compact_penalty
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T13:58:50.618328+00:00
-- url     : https://prove2.me/theorems/55826ad8-37b1-467f-891d-fb14ca1a9934
-- title:
--   Compactness makes the rank-one penalty effective (OpenAI Lieb–Thirring)
-- statement:
--   **Setting.** Fix $0 < \sigma < 1$, put $q = 1 + 1/\sigma$, fix a regularization $\delta > 0$ and a vector $k \in \mathbb R^N$, and let $K^2 = \operatorname{diag}(k_i^2)$. For a real symmetric $N \times N$ matrix $B$, `matrixField σ δ k B` is the paper's regularized field $M_\delta(B)$, a real symmetric matrix defined as a limit of truncated resolvent integrals. For a pair $z = (B, a)$, with $B$ real symmetric and $a \in \mathbb R^N$:
--   - `actionDefect σ k z` $= |a|^{2q} - a^{T}(K^2 - B^2)\,a$, with $|a|^2 = \sum_i a_i^2$;
--   - `constraintDefect σ δ k z` $= \|M_\delta(B) - a a^{T}\|_{HS}^2 = \sum_{i,j}\bigl(M_\delta(B)_{ij} - a_i a_j\bigr)^2$.
--
--   **Statement.** Let $K$ be a compact set of pairs $(B, a)$ and let $\eta > 0$. Then there is $\varepsilon_0 > 0$ such that for every $0 < \varepsilon \le \varepsilon_0$ and every $z \in K$,
--   $$\texttt{actionDefect}(z) - \frac{\texttt{constraintDefect}(z)}{\varepsilon} \le \eta .$$
--
--   This is the compactness step (6.3) in the proof of the paper's Theorem 2.1 (Section 6). As the penalty parameter $\varepsilon$ tends to zero, any point where the action defect stays positive is forced towards the rank-one constraint $M_\delta(B) = a a^T$. There the rank-one comparison (the paper's Proposition 4.1) makes the defect nonpositive. Lean: `OAI.SharpLiebThirring.ActionProof.matrix_compact_penalty`, OpenAI's lemma of that name (in `lean/OAI/Analysis/LiebThirring/ActionPenalty.lean`). The definitions come from the definitions bundle `OAIQWSLT000` of this split.
-- source:
--   OpenAI, Sharp one-dimensional Lieb–Thirring constants, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 262; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-One-Dimensional-Lieb-Thirring-Constants-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LiebThirring/ActionPenalty.lean (declaration OAI.SharpLiebThirring.ActionProof.matrix_compact_penalty)

import Mathlib
import Definitions.Def_OAIQWSLT000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u35

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open scoped NNReal

namespace SharpLiebThirring.ActionProof
open Matrix MatrixProof Set
open scoped Matrix.Norms.L2Operator
variable {N : ℕ}

lemma matrix_compact_penalty {σ δ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hδ : 0 < δ)
    (k : Fin N → ℝ)
    {K : Set (selfAdjoint (Matrix (Fin N) (Fin N) ℝ) × (Fin N → ℝ))} (hK : IsCompact K)
    {η : ℝ} (hη : 0 < η) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ z ∈ K,
      actionDefect σ k z - constraintDefect σ δ k z / ε ≤ η := by
  sorry

end SharpLiebThirring.ActionProof

end
end
end

end OAI
end
