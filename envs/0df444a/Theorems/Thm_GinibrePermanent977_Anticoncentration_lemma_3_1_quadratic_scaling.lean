-- Prove2me | Theorems.Thm_GinibrePermanent977_Anticoncentration_lemma_3_1_quadratic_scaling
-- name    : GinibrePermanent977.Anticoncentration.lemma_3_1_quadratic_scaling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:10:07.502778+00:00
-- url     : https://prove2.me/theorems/87fb5f41-919b-45f7-95e6-874ffb2d7399
-- title:
--   Lemma 3.1 — one-sided quadratic scaling of $F_{T,L}$
-- statement:
--   For $d,k\ge1$, $T\in\mathbb R^{d\times d}$, $L\in\mathbb R^{d\times k}$ and $a,b\in\mathbb R^k$ let $F_{T,L}(a,b)=E_{X,Y}\exp\bigl(i(X^*TY+X^*Lb+Y^*La)\bigr)$, where $X,Y$ are independent standard Gaussian columns in $\mathbb R^d$; $T$ need not be symmetric.
--
--   Then $F_{T,L}(a,0)$ and $F_{T,L}(0,b)$ are strictly positive real numbers, and for every $t\in\mathbb R$
--
--   $$
--   \frac{F_{T,L}(ta,0)}{F_{T,L}(0,0)}=\Bigl(\frac{F_{T,L}(a,0)}{F_{T,L}(0,0)}\Bigr)^{t^2},\qquad
--   \frac{F_{T,L}(0,tb)}{F_{T,L}(0,0)}=\Bigl(\frac{F_{T,L}(0,b)}{F_{T,L}(0,0)}\Bigr)^{t^2}.
--   $$
--
--   When only one of the linear terms is present the characteristic function is a Gaussian in that argument; this is the scaling input of the geometric interpolation (Lemma 3.2).
--
--   **Formalization Note** Positivity is stated in the order of $\mathbb C$ (the value is real and positive), so the ratios are ratios of real parts and the powers are real powers of positive numbers.
--
--   Differences from the source:
--
--   - encoding: strict positivity and the two scaling identities for $F_{T,L}$ → positivity in `ComplexOrder`, with ratios of real parts and real powers; reason: Lemma 3.1 makes all one-sided values strictly positive reals, including the scaled arguments and zero; their real parts are the same values and the denominator is nonzero
-- source:
--   Frederic Koehler, Pui Kuen Leung, STOC 2027 submission #977 (October 2026), §3.1, p. 7, Lemma 3.1 (definition of $F_{T,L}$, pp. 6–7) (PDF SHA-256 e25737f1d5e3492905f8eeaa41d92c55d95f73622a3b5846cc87aac6a346d4ec)

import Mathlib
import Definitions.Def_StochasticOrders_LaplaceTransform_LaplaceOrder
import Definitions.Def_GinibrePermanent977_Anticoncentration_Model
open MeasureTheory ProbabilityTheory Matrix
open scoped ComplexOrder Nat ENNReal

namespace GinibrePermanent977.Anticoncentration

/-- Lemma 3.1 (One-sided quadratic scaling), p. 7. For `d, k ≥ 1`, `T ∈ ℝ^{d×d}`,
`L ∈ ℝ^{d×k}`, `a, b ∈ ℝ^k`: `F_{T,L}(a, 0)` and `F_{T,L}(0, b)` are strictly positive reals, and
for every real `t`, `F(ta,0)/F(0,0) = (F(a,0)/F(0,0))^{t²}` and `F(0,tb)/F(0,0) = (F(0,b)/F(0,0))^{t²}`.
`0 < w` is the order of `ℂ` (`w` real and positive), so the ratios are ratios of real parts. -/
theorem lemma_3_1_quadratic_scaling {d k : ℕ} (hd : 1 ≤ d) (hk : 1 ≤ k)
    (T : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ) (a b : Fin k → ℝ) :
    0 < bilinChar T L a 0 ∧ 0 < bilinChar T L 0 b ∧
      ∀ t : ℝ,
        (bilinChar T L (t • a) 0).re / (bilinChar T L 0 0).re =
            ((bilinChar T L a 0).re / (bilinChar T L 0 0).re) ^ (t ^ 2) ∧
          (bilinChar T L 0 (t • b)).re / (bilinChar T L 0 0).re =
            ((bilinChar T L 0 b).re / (bilinChar T L 0 0).re) ^ (t ^ 2) := by sorry

end GinibrePermanent977.Anticoncentration
