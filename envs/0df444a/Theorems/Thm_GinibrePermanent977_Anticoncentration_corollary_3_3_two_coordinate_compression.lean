-- Prove2me | Theorems.Thm_GinibrePermanent977_Anticoncentration_corollary_3_3_two_coordinate_compression
-- name    : GinibrePermanent977.Anticoncentration.corollary_3_3_two_coordinate_compression
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:10:16.848461+00:00
-- url     : https://prove2.me/theorems/c2157fec-6b03-432a-914e-d963930f4c2c
-- title:
--   Corollary 3.3 — Gaussian two-coordinate compression
-- statement:
--   For $d,k\ge1$, $T\in\mathbb R^{d\times d}$, $L\in\mathbb R^{d\times k}$ and $a,b\in\mathbb R^k$ let $F_{T,L}(a,b)=E_{X,Y}\exp\bigl(i(X^*TY+X^*Lb+Y^*La)\bigr)$, where $X,Y$ are independent standard Gaussian columns in $\mathbb R^d$; $T$ need not be symmetric.
--
--   Let $(T,L)$ be jointly random, with an arbitrary joint law on $\mathbb R^{d\times d}\times\mathbb R^{d\times k}$ (no independence, boundedness or moment assumption). For every $a,b\in\mathbb R^k$ and $\theta\in[0,1]$,
--
--   $$
--   E_{T,L}\Bigl|F_{T,L}\bigl(\sqrt\theta\,a,\sqrt{1-\theta}\,b\bigr)\Bigr|
--   \le\bigl(E_{T,L}F_{T,L}(a,0)\bigr)^{\theta}\bigl(E_{T,L}F_{T,L}(0,b)\bigr)^{1-\theta}
--   \le\max\bigl\{E_{T,L}F_{T,L}(a,0),\,E_{T,L}F_{T,L}(0,b)\bigr\}.
--   $$
--
--   Averaged over random bilinear and linear coefficients, mixing two coordinates never concentrates the characteristic function more than the better of the two single-coordinate endpoints.
--
--   **Formalization Note** The joint law is a probability measure $\rho$ on pairs of real matrices; $E_{T,L}F_{T,L}(a,0)$ is the integral of the real part of $F_{T,L}(a,0)$, which is its value by Lemma 3.1. All integrands have modulus at most $1$.
--
--   Differences from the source:
--
--   - encoding: jointly random matrices $T,L$ → an arbitrary probability measure $\rho$ on $\mathbb R^{d\times d}\times\mathbb R^{d\times k}$, expectations as integrals of real parts; reason: the statement depends only on the joint law; $F_{T,L}(a,0)$ and $F_{T,L}(0,b)$ are real by Lemma 3.1
-- source:
--   Frederic Koehler, Pui Kuen Leung, STOC 2027 submission #977 (October 2026), §3.1, p. 8, Corollary 3.3 (PDF SHA-256 e25737f1d5e3492905f8eeaa41d92c55d95f73622a3b5846cc87aac6a346d4ec)

import Mathlib
import Definitions.Def_StochasticOrders_LaplaceTransform_LaplaceOrder
import Definitions.Def_GinibrePermanent977_Anticoncentration_Model
open MeasureTheory ProbabilityTheory Matrix
open scoped ComplexOrder Nat ENNReal

namespace GinibrePermanent977.Anticoncentration

/-- Corollary 3.3 (Gaussian two-coordinate compression), p. 8. Let `(T, L)` be jointly random,
with arbitrary joint law `ρ` on `ℝ^{d×d} × ℝ^{d×k}` (`d, k ≥ 1`). For every `a, b ∈ ℝ^k` and
`θ ∈ [0, 1]`,
`E|F_{T,L}(√θ a, √(1-θ) b)| ≤ (E F_{T,L}(a,0))^θ (E F_{T,L}(0,b))^{1-θ}
  ≤ max {E F_{T,L}(a,0), E F_{T,L}(0,b)}`. -/
theorem corollary_3_3_two_coordinate_compression {d k : ℕ} (hd : 1 ≤ d) (hk : 1 ≤ k)
    (ρ : Measure ((Fin d → Fin d → ℝ) × (Fin d → Fin k → ℝ))) [IsProbabilityMeasure ρ]
    (a b : Fin k → ℝ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∫ q, ‖bilinChar (Matrix.of q.1) (Matrix.of q.2) (Real.sqrt θ • a)
        (Real.sqrt (1 - θ) • b)‖ ∂ρ ≤
      (∫ q, (bilinChar (Matrix.of q.1) (Matrix.of q.2) a 0).re ∂ρ) ^ θ *
        (∫ q, (bilinChar (Matrix.of q.1) (Matrix.of q.2) 0 b).re ∂ρ) ^ (1 - θ) ∧
    (∫ q, (bilinChar (Matrix.of q.1) (Matrix.of q.2) a 0).re ∂ρ) ^ θ *
        (∫ q, (bilinChar (Matrix.of q.1) (Matrix.of q.2) 0 b).re ∂ρ) ^ (1 - θ) ≤
      max (∫ q, (bilinChar (Matrix.of q.1) (Matrix.of q.2) a 0).re ∂ρ)
        (∫ q, (bilinChar (Matrix.of q.1) (Matrix.of q.2) 0 b).re ∂ρ) := by sorry

end GinibrePermanent977.Anticoncentration
