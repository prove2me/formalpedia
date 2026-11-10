-- Prove2me | Theorems.Thm_GinibrePermanent977_Anticoncentration_lemma_3_2_geometric_interpolation
-- name    : GinibrePermanent977.Anticoncentration.lemma_3_2_geometric_interpolation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:10:15.342047+00:00
-- url     : https://prove2.me/theorems/0995d792-adb8-4440-8965-b0f740aee0ea
-- title:
--   Lemma 3.2 — Gaussian geometric interpolation
-- statement:
--   For $d,k\ge1$, $T\in\mathbb R^{d\times d}$, $L\in\mathbb R^{d\times k}$ and $a,b\in\mathbb R^k$ let $F_{T,L}(a,b)=E_{X,Y}\exp\bigl(i(X^*TY+X^*Lb+Y^*La)\bigr)$, where $X,Y$ are independent standard Gaussian columns in $\mathbb R^d$; $T$ need not be symmetric.
--
--   For every such $T,L,a,b$ and every $\theta\in[0,1]$,
--
--   $$
--   \Bigl|F_{T,L}\bigl(\sqrt\theta\,a,\sqrt{1-\theta}\,b\bigr)\Bigr|=F_{T,L}(a,0)^{\theta}\,F_{T,L}(0,b)^{1-\theta}.
--   $$
--
--   The right side is a weighted geometric mean of the two one-sided values, which are positive reals by Lemma 3.1. The identity is the exact two-column interpolation behind the compression argument of Corollary 3.3 and Proposition 3.5.
--
--   Differences from the source:
--
--   - encoding: powers of the positive one-sided values $F_{T,L}(a,0)$ and $F_{T,L}(0,b)$ → real powers of their real parts; reason: Lemma 3.1 identifies these values with strictly positive real numbers, so taking real parts changes no value or instance
-- source:
--   Frederic Koehler, Pui Kuen Leung, STOC 2027 submission #977 (October 2026), §3.1, p. 7, Lemma 3.2 (PDF SHA-256 e25737f1d5e3492905f8eeaa41d92c55d95f73622a3b5846cc87aac6a346d4ec)

import Mathlib
import Definitions.Def_StochasticOrders_LaplaceTransform_LaplaceOrder
import Definitions.Def_GinibrePermanent977_Anticoncentration_Model
open MeasureTheory ProbabilityTheory Matrix
open scoped ComplexOrder Nat ENNReal

namespace GinibrePermanent977.Anticoncentration

/-- Lemma 3.2 (Gaussian geometric interpolation), p. 7. For `d, k ≥ 1`, every `T, L, a, b` and
`θ ∈ [0, 1]`, `|F_{T,L}(√θ a, √(1-θ) b)| = F_{T,L}(a, 0)^θ F_{T,L}(0, b)^{1-θ}` (the right side
uses the real values of the positive quantities of Lemma 3.1). -/
theorem lemma_3_2_geometric_interpolation {d k : ℕ} (hd : 1 ≤ d) (hk : 1 ≤ k)
    (T : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ) (a b : Fin k → ℝ)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ‖bilinChar T L (Real.sqrt θ • a) (Real.sqrt (1 - θ) • b)‖ =
      (bilinChar T L a 0).re ^ θ * (bilinChar T L 0 b).re ^ (1 - θ) := by sorry

end GinibrePermanent977.Anticoncentration
