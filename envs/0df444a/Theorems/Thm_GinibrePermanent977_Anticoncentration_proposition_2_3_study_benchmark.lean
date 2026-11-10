-- Prove2me | Theorems.Thm_GinibrePermanent977_Anticoncentration_proposition_2_3_study_benchmark
-- name    : GinibrePermanent977.Anticoncentration.proposition_2_3_study_benchmark
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:10:26.78205+00:00
-- url     : https://prove2.me/theorems/d4f75d85-3247-4219-b079-53dd1d2af6b7
-- title:
--   Proposition 2.3 — Study determinant benchmark
-- statement:
--   Let $G_n^{\mathbb H}$ be a standard quaternionic Ginibre matrix, $\operatorname{Sdet}$ the Study determinant (product of the quaternionic singular values) and $\gamma_{k,4}\sim\mathrm{Gamma}(2k,1/2)$ (shape, scale) independent. For every $n\ge1$,
--
--   $$
--   \operatorname{Sdet}(G_n^{\mathbb H})^2\overset d=\prod_{k=1}^n\gamma_{k,4}\quad(11),\qquad
--   \Delta_n^{\mathbb H}=\frac{\operatorname{Sdet}(G_n^{\mathbb H})^2}{n!}\overset d=\prod_{k=1}^n\frac{\gamma_{k,4}}{k}\quad(12).
--   $$
--
--   Over $\mathbb H$ the Study determinant realizes the same gamma benchmark as the determinant over $\mathbb R$ and $\mathbb C$.
--
--   Differences from the source:
--
--   - encoding: random variables (independent Gaussian/gamma variables) → functions on the canonical product sample spaces `ginibre`, `gammaVec`, `benchLaw`; reason: independence is encoded by product measures; same laws
--   - encoding: $=_d$ → `IdentDistrib` (equal laws, both maps a.e. measurable); reason: the compared maps use polynomial operations, norms and measurable real roots; measurability adds no hypothesis and the laws are unchanged
--   - encoding: $\operatorname{Sdet}A=\prod_j\sigma_j(A)$ (singular values) → `studyDet A` $=\det_{\mathbb R}(v\mapsto Av)^{1/4}$; reason: identity $\det_{\mathbb R}(A)=\operatorname{Sdet}(A)^4$ stated on p. 6; holds for every $A$, and $\det_{\mathbb R}\ge0$
-- source:
--   Frederic Koehler, Pui Kuen Leung, STOC 2027 submission #977 (October 2026), §2, p. 6, Proposition 2.3, Eqs. (11)–(12); Definition 2.2, p. 5 (PDF SHA-256 e25737f1d5e3492905f8eeaa41d92c55d95f73622a3b5846cc87aac6a346d4ec)

import Mathlib
import Definitions.Def_StochasticOrders_LaplaceTransform_LaplaceOrder
import Definitions.Def_GinibrePermanent977_Anticoncentration_Model
open MeasureTheory ProbabilityTheory Matrix
open scoped ComplexOrder Nat ENNReal

namespace GinibrePermanent977.Anticoncentration

/-- Proposition 2.3 (Study determinant benchmark), p. 6. For every `n ≥ 1`, with `G_n^ℍ` a standard
quaternionic Ginibre matrix and `γ_{k,4} ∼ Gamma(2k, 1/2)` (shape, scale) independent:
(11) `Sdet(G_n^ℍ)² =_d ∏_{k=1}^n γ_{k,4}`;
(12) `Δ_n^ℍ = Sdet(G_n^ℍ)²/n! =_d ∏_{k=1}^n γ_{k,4}/k`. -/
theorem proposition_2_3_study_benchmark (n : ℕ) (hn : 1 ≤ n) :
    IdentDistrib (fun G : Fin n → Fin n → Scalar.quaternion.K => studyDet G ^ 2)
        (fun γ : Fin n → ℝ => ∏ k, γ k)
        (ginibre Scalar.quaternion n n) (gammaVec Scalar.quaternion n) ∧
      IdentDistrib (fun G : Fin n → Fin n → Scalar.quaternion.K => studyDet G ^ 2 / (n ! : ℝ))
        (fun γ : Fin n → ℝ => ∏ k, γ k / ((k : ℕ) + 1 : ℝ))
        (ginibre Scalar.quaternion n n) (gammaVec Scalar.quaternion n) := by sorry

end GinibrePermanent977.Anticoncentration
