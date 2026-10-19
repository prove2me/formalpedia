-- Prove2me | Theorems.Thm_OAI_CrouzeixHilbert_Disk_integral_matrixHolomorphic
-- name    : OAI.CrouzeixHilbert.Disk.integral_matrixHolomorphic
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T00:42:55.296577+00:00
-- url     : https://prove2.me/theorems/c3ad5d57-eb0d-4838-b97f-68ffdd7c3970
-- title:
--   Poisson-type boundary representation of matrix-valued holomorphic evaluation of a contraction with spectral radius below 1 (OpenAI complete Crouzeix theorem)
-- statement:
--   Let $H$ be a complex Hilbert space and $D$ a bounded operator on $H$ with $\|D\| \le 1$ and spectral radius $\rho(D) < 1$ (`spectralRadius ℂ D < 1`). For $t$ in the circle $\mathbb T = \mathbb R/\mathbb Z$ (`CircleSpace`) write $e_1(t) = e^{2\pi i t}$ (`fourier 1 t`) and let
--   $$\varphi_D(t) = (1 - e_1(t)^{-1} D)^{-1} + \bigl((1 - e_1(t)^{-1} D)^{-1}\bigr)^* - 1$$
--   (`phi D t`, definitions bundle `OAIQWCH000`, with `Ring.inverse` for the inverse). Let $U$ be an open set containing the closed unit disc, $m$ a natural number and $F : \mathbb C \to M_m(\mathbb C)$ entrywise holomorphic on $U$ (`EntrywiseHolomorphic U F`). Then, integrating with the normalized Haar measure $\sigma$ of the circle,
--   $$\int_{\mathbb T} \varphi_D(t) \otimes F\bigl(e_1(t)\bigr)\, d\sigma(t) \;=\; F[D],$$
--   where $\otimes$ is `tensorOperator` and $F[D]$ is the holomorphic functional calculus with matrix coefficients `matrixHolomorphicEval D U F` (both from the published bundle `Def_CrouzeixHilbert`). The integral is a Bochner integral in the space of operators on $H \otimes \mathbb C^m$, with the real normed-space structure the statement activates as a local instance.
--
--   Lean: `OAI.CrouzeixHilbert.Disk.integral_matrixHolomorphic`, OpenAI's theorem of that name (in `lean/OAI/Analysis/Crouzeix/DiskHolomorphic.lean`). It is published as an intermediate statement of this split because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, The complete Crouzeix theorem: optimal similarity and a common positive boundary representation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 325; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-complete-Crouzeix-theorem-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Crouzeix/DiskHolomorphic.lean (declaration OAI.CrouzeixHilbert.Disk.integral_matrixHolomorphic)

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

open MeasureTheory Set Filter

open scoped Topology TensorProduct Matrix.Norms.L2Operator

namespace CrouzeixHilbert

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Disk

attribute [local instance] OAI.CrouzeixHilbert.diskHolomorphicOperatorRealNormedSpace
local instance diskHolomorphicFactZeroLtOne_rcf722c_1 : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
theorem integral_matrixHolomorphic (D : Operator H) (hN : ‖D‖ ≤ 1)
    (hD : spectralRadius ℂ D < 1) {m : ℕ} {U : Set ℂ} {F : ℂ → Coeff m}
    (hU : IsOpen U) (hKU : Metric.closedBall (0 : ℂ) 1 ⊆ U)
    (hF : EntrywiseHolomorphic U F) :
    (∫ t : CircleSpace, tensorOperator (phi D t) (F (fourier 1 t)) ∂σ) =
      matrixHolomorphicEval D U F := by
  sorry

end Disk

end CrouzeixHilbert

end

end OAI
end
