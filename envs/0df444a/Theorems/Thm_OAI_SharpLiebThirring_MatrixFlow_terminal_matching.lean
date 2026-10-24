-- Prove2me | Theorems.Thm_OAI_SharpLiebThirring_MatrixFlow_terminal_matching
-- name    : OAI.SharpLiebThirring.MatrixFlow.terminal_matching
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T13:59:22.054978+00:00
-- url     : https://prove2.me/theorems/5e79d436-a081-428d-a526-1ac2bd795389
-- title:
--   A matrix flow from K to −K driven by a lower-triangular forcing (OpenAI Lieb–Thirring)
-- statement:
--   **Setting.** `Sym N` is the space of real symmetric $N \times N$ matrices. `symDiag k` is the diagonal matrix $\operatorname{diag}(k_1, \dots, k_N)$, `symOuter a` is $a a^{\mathsf T}$, and `symConj s A` is $(s_i A_{ij} s_j)_{ij}$, conjugation by the diagonal matrix of $s$. `LowerSpace N` is the space of real lower-triangular $N \times N$ matrices.
--
--   **Statement.** Let $l \le r$ and $\varepsilon > 0$. Let $M : \mathrm{Sym}_N \to \mathrm{Sym}_N$ be Lipschitz and bounded, $\|M(A)\| \le B$, with two structural properties:
--   - **sign equivariance:** $M(SAS) = S\,M(A)\,S$ for every diagonal sign matrix $S$;
--   - **decoupled rows:** there are a bounded $q : \mathrm{Sym}_N \to \mathbb R$ and locally Lipschitz $g_i : \mathbb R \to \mathbb R$ such that, whenever row $i$ of $A$ vanishes off the diagonal, $M(A)_{ii} = q(A)\,g_i(A_{ii})$.
--
--   Let $k_i > 0$ with $g_i(k_i) = 0$. Let $u : \mathbb R \to \mathbb R^N$ be continuous on $[l, r]$ with orthonormal components, $\int_l^r u_i u_j = \delta_{ij}$. Then there are a lower-triangular $C$ and a path $X$ in $\mathrm{Sym}_N$ with
--   $$X(l) = \operatorname{diag}(k), \qquad X(r) = -\operatorname{diag}(k), \qquad \varepsilon X'(t) = M(X(t)) - (C u(t))(C u(t))^{\mathsf T} \quad (t \in [l, r]),$$
--   the derivative taken within $[l, r]$, and, with the operator norm on matrices and the sup norm on $k$,
--   $$\|C C^{\mathsf T}\| \le 2\varepsilon\,\|k\| + (r - l)\,B .$$
--
--   This is the terminal matching problem in the paper's proof of Proposition 5.1 (connecting path): the paths (5.4) for a bounded Lipschitz field $M$, which plays the role of the cut-off field $\widehat M = \chi M_\delta$ of (5.6), with the decoupling hypothesis in the role of (5.3). The lower-triangular $C$ is found by continuation in a parameter and parity modulo row signs. Lean: `OAI.SharpLiebThirring.MatrixFlow.terminal_matching`, OpenAI's lemma of that name (in lean/OAI/Analysis/LiebThirring/FlowContinuation.lean). The definitions (`Sym`, `symDiag`, `symOuter`, `symConj`, `LowerSpace`) come from the definitions bundle `OAIQWSLT000` of this split; `LocallyLipschitz` is Mathlib's.
-- source:
--   OpenAI, Sharp one-dimensional Lieb–Thirring constants, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 262; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-One-Dimensional-Lieb-Thirring-Constants-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LiebThirring/FlowContinuation.lean (declaration OAI.SharpLiebThirring.MatrixFlow.terminal_matching)

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

namespace SharpLiebThirring.MatrixFlow
open ODEProof Set Matrix ContinuationGap
variable {N : ℕ}

lemma terminal_matching {l r ε : ℝ} (hlr : l ≤ r) (hε : 0 < ε)
    (M : Sym N → Sym N) (L B Q : ℝ≥0) (hL : LipschitzWith L M) (hB : ∀ A, ‖M A‖ ≤ B)
    (q : Sym N → ℝ) (hq : ∀ A, |q A| ≤ Q)
    (g : Fin N → ℝ → ℝ) (hg : ∀ i, LocallyLipschitz (g i))
    (k : Fin N → ℝ) (hk : ∀ i, 0 < k i) (hgk : ∀ i, g i (k i) = 0)
    (hc : ∀ i A, (∀ j, i ≠ j → A.val i j = 0) → (M A).val i i = q A * g i (A.val i i))
    (he : ∀ s : Fin N → ℝ, (∀ i, s i = 1 ∨ s i = -1) → ∀ A, M (symConj s A) = symConj s (M A))
    (u : ℝ → Fin N → ℝ) (hu : ContinuousOn u (Icc l r))
    (ho : ∀ i j, (∫ t in l..r, u t i * u t j) = if i=j then 1 else 0) :
    ∃ (C : LowerSpace N) (X : ℝ → Sym N), X l = symDiag k ∧ X r = -symDiag k ∧
      (∀ t ∈ Icc l r, HasDerivWithinAt X (ε⁻¹ • (M (X t) - symOuter (C.val *ᵥ u t))) (Icc l r) t) ∧
      ‖C.val * C.val.transpose‖ ≤ |ε| * (2*‖k‖) + (r-l)*B := by
  sorry

end SharpLiebThirring.MatrixFlow

end
end
end
end
end

end OAI
end
