-- Prove2me | Theorems.Thm_OAI_CrouzeixHilbert_disk_endpoint_extremal
-- name    : OAI.CrouzeixHilbert.disk_endpoint_extremal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T00:43:20.623816+00:00
-- url     : https://prove2.me/theorems/69b4dce5-2c4b-454a-95c9-ff92f24b38e0
-- title:
--   Extremal vectors and a rational extremal function for the optimal Stein metric of a matrix with spectral radius below 1 (OpenAI complete Crouzeix theorem)
-- statement:
--   For matrices $T, H \in M_n(\mathbb C)$ and $\tau \in \mathbb R$, `Metric.Feasible T τ H` (definitions bundle `OAIQWCH000`) means $I \preceq H \preceq \tau I$ and $T^* H T \preceq H$ in the Loewner order.
--
--   Let $n \ge 1$, let $T \in M_n(\mathbb C)$ have spectral radius $\rho(T) < 1$, and let $\kappa > 1$ be real. Suppose $H$ is feasible with $\tau = \kappa^2$ and that $\kappa^2$ is minimal: $\kappa^2 \le s$ whenever some $J$ is feasible with $\tau = s$. Write $S = H^{1/2}$ (`CFC.sqrt H`) and $T' = S T S^{-1}$ (with `Ring.inverse`). Then there are matrices $X, Y \in M_n(\mathbb C)$, an $n \times n$ matrix of rational functions $R$ (`RationalMatrix n`) and an open set $U \subseteq \mathbb C$ such that
--   - $\operatorname{tr}(XX^*) = 1$, $\operatorname{tr}(YY^*) = 1$, $SX = \kappa X$, $SY = Y$ and $X^* Y = 0$;
--   - the vectorizations $\operatorname{vec} X, \operatorname{vec} Y \in \mathbb C^n \otimes \mathbb C^n$ (`vectorization`) have norm $1$, and $(S \otimes I)\operatorname{vec} X = \kappa \operatorname{vec} X$, $(S \otimes I)\operatorname{vec} Y = \operatorname{vec} Y$ (`tensorOperator`);
--   - $U$ is open and contains the closed unit disc, the poles of $R$ lie outside $U$ (`PolesOutside U R`), the matrix function $z \mapsto R(z)$ is entrywise holomorphic on $U$ (`EntrywiseHolomorphic`) and has operator norm at most $1$ for $|z| \le 1$;
--   - $R[T'] \operatorname{vec} X = \operatorname{vec} Y$ both for the rational functional calculus (`matrixRationalEval`) and for the holomorphic functional calculus on $U$ (`matrixHolomorphicEval`).
--
--   These are the extremal data of the minimal Stein metric used in Section 3 of OpenAI's paper.
--
--   Lean: `OAI.CrouzeixHilbert.disk_endpoint_extremal`, OpenAI's theorem of that name (in `lean/OAI/Analysis/Crouzeix/DiskEndpoint.lean`). `Coeff`, `tensorOperator`, `RationalMatrix`, `PolesOutside`, `EntrywiseHolomorphic`, `matrixRationalFunction`, `matrixRationalEval` and `matrixHolomorphicEval` come from the published bundle `Def_CrouzeixHilbert`; `Metric.Feasible` and `vectorization` from the definitions bundle `OAIQWCH000`. It is published as an intermediate statement of this split because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, The complete Crouzeix theorem: optimal similarity and a common positive boundary representation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 325; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-complete-Crouzeix-theorem-September-23-2026/paper.pdf, Section 3; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Crouzeix/DiskEndpoint.lean (declaration OAI.CrouzeixHilbert.disk_endpoint_extremal)

import Mathlib
import Definitions.Def_CrouzeixHilbert
import Definitions.Def_OAIQWCH000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set

open scoped TensorProduct Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder InnerProductSpace

namespace CrouzeixHilbert

open Boundary Realization Endpoint

theorem disk_endpoint_extremal {n : ℕ} (hn : 0 < n) (T : Coeff n)
    (hT : spectralRadius ℂ T < 1) {κ : ℝ} (hκ : 1 < κ)
    (H : Coeff n) (hH : Metric.Feasible T (κ ^ 2) H)
    (hmin : ∀ s J, Metric.Feasible T s J → κ ^ 2 ≤ s) :
    ∃ (X Y : Coeff n) (R : RationalMatrix n) (U : Set ℂ),
      (X * Xᴴ).trace = 1 ∧ (Y * Yᴴ).trace = 1 ∧
      CFC.sqrt H * X = κ • X ∧ CFC.sqrt H * Y = Y ∧ Xᴴ * Y = 0 ∧
      ‖vectorization X‖ = 1 ∧ ‖vectorization Y‖ = 1 ∧
      tensorOperator (Matrix.toEuclideanCLM (𝕜 := ℂ) (CFC.sqrt H)) (1 : Coeff n)
        (vectorization X) = (κ : ℂ) • vectorization X ∧
      tensorOperator (Matrix.toEuclideanCLM (𝕜 := ℂ) (CFC.sqrt H)) (1 : Coeff n)
        (vectorization Y) = vectorization Y ∧
      IsOpen U ∧ Metric.closedBall (0 : ℂ) 1 ⊆ U ∧ PolesOutside U R ∧
      EntrywiseHolomorphic U (matrixRationalFunction R) ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → ‖matrixRationalFunction R z‖ ≤ 1) ∧
      matrixRationalEval (Matrix.toEuclideanCLM (𝕜 := ℂ)
        (CFC.sqrt H * T * Ring.inverse (CFC.sqrt H))) R
          (vectorization X) = vectorization Y ∧
      matrixHolomorphicEval (Matrix.toEuclideanCLM (𝕜 := ℂ)
        (CFC.sqrt H * T * Ring.inverse (CFC.sqrt H))) U
          (matrixRationalFunction R) (vectorization X) = vectorization Y := by
  sorry

end CrouzeixHilbert

end

end OAI
end
