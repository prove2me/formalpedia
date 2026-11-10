-- Prove2me | Theorems.Thm_GinibrePermanent977_Anticoncentration_theorem_3_7_study_permanent_comparison
-- name    : GinibrePermanent977.Anticoncentration.theorem_3_7_study_permanent_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:10:39.191206+00:00
-- url     : https://prove2.me/theorems/71360a70-ab38-4a56-918c-d8990e8a873c
-- title:
--   Theorem 3.7 — Study determinant–permanent comparison
-- statement:
--   Let $G_n^{\mathbb H}$ be a standard quaternionic Ginibre matrix, $\operatorname{per}_{\mathbb H}$ the row-ordered permanent and $\operatorname{Sdet}$ the Study determinant. For every $n\ge1$,
--
--   $$
--   \operatorname{Sdet}(G_n^{\mathbb H})^2\le_{Lt}|\operatorname{per}_{\mathbb H}G_n^{\mathbb H}|^2\quad(18);
--   $$
--
--   equivalently $\Delta_n^{\mathbb H}\le_{Lt}X_n^{\mathbb H}$, where $\Delta_n^{\mathbb H}=\operatorname{Sdet}(G_n^{\mathbb H})^2/n!$ and $X_n^{\mathbb H}=|W_n^{\mathbb H}|^2=|\operatorname{per}_{\mathbb H}G_n^{\mathbb H}|^2/n!$.
--
--   This is the quaternionic counterpart of Theorem 1.5 (5), the comparison used for the density bound over $\mathbb H$. Both forms are stated.
--
--   Differences from the source:
--
--   - encoding: random variables (independent Gaussian/gamma variables) → functions on the canonical product sample spaces `ginibre`, `gammaVec`, `benchLaw`; reason: independence is encoded by product measures; same laws
--   - encoding: $U\le_{Lt}V$: $Ee^{-sU}\ge Ee^{-sV}$ for $s\ge0$ → published `LaplaceOrder`, quantified over $s>0$; reason: at $s=0$ both sides equal 1 for probability laws; same order
--   - encoding: $\operatorname{Sdet}A=\prod_j\sigma_j(A)$ (singular values) → `studyDet A` $=\det_{\mathbb R}(v\mapsto Av)^{1/4}$; reason: identity $\det_{\mathbb R}(A)=\operatorname{Sdet}(A)^4$ stated on p. 6; holds for every $A$, and $\det_{\mathbb R}\ge0$
-- source:
--   Frederic Koehler, Pui Kuen Leung, STOC 2027 submission #977 (October 2026), §3.4, p. 11, Theorem 3.7, Eq. (18) (PDF SHA-256 e25737f1d5e3492905f8eeaa41d92c55d95f73622a3b5846cc87aac6a346d4ec)

import Mathlib
import Definitions.Def_StochasticOrders_LaplaceTransform_LaplaceOrder
import Definitions.Def_GinibrePermanent977_Anticoncentration_Model
open MeasureTheory ProbabilityTheory Matrix
open scoped ComplexOrder Nat ENNReal

namespace GinibrePermanent977.Anticoncentration

/-- Theorem 3.7 (Study determinant–permanent comparison), p. 11. For every `n ≥ 1`,
(18) `Sdet(G_n^ℍ)² ≤_{Lt} |per_ℍ G_n^ℍ|²`; equivalently `Δ_n^ℍ ≤_{Lt} X_n^ℍ`, where
`Δ_n^ℍ = Sdet(G_n^ℍ)²/n!` and `X_n^ℍ = |W_n^ℍ|² = |per_ℍ G_n^ℍ|²/n!`. -/
theorem theorem_3_7_study_permanent_comparison (n : ℕ) (hn : 1 ≤ n) :
    StochasticOrders.LaplaceTransform.LaplaceOrder (ginibre Scalar.quaternion n n)
        (ginibre Scalar.quaternion n n)
        (fun G => studyDet G ^ 2) (fun G => ‖perK G‖ ^ 2) ∧
      StochasticOrders.LaplaceTransform.LaplaceOrder (ginibre Scalar.quaternion n n)
        (ginibre Scalar.quaternion n n)
        (fun G => studyDet G ^ 2 / (n ! : ℝ)) (fun G => ‖normPer G‖ ^ 2) := by sorry

end GinibrePermanent977.Anticoncentration
