-- Prove2me | Theorems.Thm_OAI_SharpLiebThirring_ActionProof_regularized_action_upper_test
-- name    : OAI.SharpLiebThirring.ActionProof.regularized_action_upper_test
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T13:58:51.987703+00:00
-- url     : https://prove2.me/theorems/3e6ce247-fd0a-4442-90f8-095e3f165b0f
-- title:
--   Regularized action inequality on a finite interval (OpenAI Lieb–Thirring)
-- statement:
--   **Setting.** Fix $0 < \sigma < 1$, put $q = 1 + 1/\sigma$, fix $\delta > 0$ and $k \in \mathbb R^N$ with every $k_i > 0$, and write $K = \operatorname{diag}(k_i)$. The action density of an amplitude $a \in \mathbb R^N$ with velocity $v \in \mathbb R^N$ is
--   $$\texttt{actionDensity}(a, v) = |v|^2 + \sum_i k_i^2 a_i^2 - |a|^{2q},$$
--   with $|a|^2 = \sum_i a_i^2$. `fieldPrimitive σ δ k B` is the paper's primitive $J_\delta(B) = -\int_0^1 \operatorname{tr}\bigl(B\,M_\delta(tB)\bigr)\,dt$ of the regularized field $M_\delta$, for a real $N \times N$ matrix $B$. `LowerSpace N` is the space of real lower triangular $N \times N$ matrices.
--
--   **Statement.** Let $l \le r$, and let $u, v : \mathbb R \to \mathbb R^N$ be continuous on $[l, r]$, with $u_i' = v_i$ on $(l, r)$, $u(l) = u(r) = 0$, and
--   $$\int_l^r u_i\,u_j\,dt = \delta_{ij} \qquad (1 \le i, j \le N).$$
--   If $S$ bounds the action of every lower triangular combination, that is $\int_l^r \texttt{actionDensity}(C u(t), C v(t))\,dt \le S$ for every lower triangular $C$, then
--   $$J_\delta(-K) - J_\delta(K) \le S .$$
--
--   This is the action inequality at a fixed regularization $\delta$, the inequality established in the proof of the paper's Theorem 2.1 (Section 6) before $\delta \downarrow 0$. The rows $u_i$ are an orthonormal family of trial functions vanishing at the ends of the interval. Lean: `OAI.SharpLiebThirring.ActionProof.regularized_action_upper_test`, OpenAI's lemma of that name (in `lean/OAI/Analysis/LiebThirring/IntervalAction.lean`). The definitions come from the definitions bundle `OAIQWSLT000` of this split.
-- source:
--   OpenAI, Sharp one-dimensional Lieb–Thirring constants, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 262; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-One-Dimensional-Lieb-Thirring-Constants-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LiebThirring/IntervalAction.lean (declaration OAI.SharpLiebThirring.ActionProof.regularized_action_upper_test)

import Mathlib
import Definitions.Def_OAIQWSLT000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology NNReal
noncomputable section
open Matrix Set MeasureTheory WithLp
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
open Set Metric
open scoped NNReal
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator

namespace SharpLiebThirring.ActionProof
open Matrix MatrixProof MatrixFlow MeasureTheory Set Filter ContinuationGap
open scoped Matrix.Norms.L2Operator Topology
variable {N : ℕ}

lemma regularized_action_upper_test {σ δ l r S : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hδ : 0 < δ) (hlr : l ≤ r) (k : Fin N → ℝ) (hk : ∀ i, 0 < k i)
    (u v : ℝ → Fin N → ℝ) (hu : ContinuousOn u (Icc l r)) (hv : ContinuousOn v (Icc l r))
    (hud : ∀ t ∈ Ioo l r, ∀ i, HasDerivAt (fun t ↦ u t i) (v t i) t)
    (hul : u l = 0) (hur : u r = 0)
    (ho : ∀ i j, (∫ t in l..r, u t i*u t j) = if i=j then 1 else 0)
    (hS : ∀ C : LowerSpace N,
      (∫ t in l..r, actionDensity σ k (C.val *ᵥ u t) (C.val *ᵥ v t)) ≤ S) :
    fieldPrimitive σ δ k (-diagonal k) - fieldPrimitive σ δ k (diagonal k) ≤ S := by
  sorry

end SharpLiebThirring.ActionProof

end

end

end

end

end

end

end

end OAI
end
