-- Prove2me | Theorems.Thm_GinibrePermanent977_Anticoncentration_Supplement_theorem_C_1
-- name    : GinibrePermanent977.Anticoncentration.Supplement.theorem_C_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:39:03.581413+00:00
-- url     : https://prove2.me/theorems/7bab5638-d5ae-41aa-adc4-3441d96eb14f
-- title:
--   Theorem C.1 — Independent-row comparison
-- statement:
--   Let $\mathbb K\in\{\mathbb R,\mathbb C,\mathbb H\}$, $\beta=\dim_{\mathbb R}\mathbb K$, and $n\ge1$. Let $A$ have mutually independent rows $R_i$, with arbitrary dependence among the coordinates of each row. Suppose $\sigma_i>0$ and
--   $$(36)\qquad ER_i^*R_i=\sigma_i^2I_n,\qquad \gamma_{1,\beta}\le_{\mathrm{Lt}}\frac{|R_ic|^2}{\sigma_i^2\|c\|_2^2}\quad(c\in\mathbb K^n\setminus\{0\}).$$
--   Here $R_ic=\sum_jR_{i,j}c_j$ uses right coefficients without conjugating the row, and $\gamma_{1,\beta}$ has gamma shape $\beta/2$ and scale $2/\beta$. Put $X_n=|\operatorname{per}_{\mathbb K}G|^2/n!$, and let $\Delta_n$ be the normalized squared determinant of $G$ over the real and complex fields or normalized squared Study determinant over quaternions. Then both links hold:
--   $$(37)\qquad\Delta_n\le_{\mathrm{Lt}}X_n\le_{\mathrm{Lt}}\frac{|\operatorname{per}_{\mathbb K}A|^2}{n!\prod_i\sigma_i^2}.$$
--   The exact finite second moment is
--   $$E|\operatorname{per}_{\mathbb K}A|^2=n!\prod_i\sigma_i^2.$$
--   For every $\varepsilon>0$,
--   $$(38)\qquad P\left(|\operatorname{per}_{\mathbb K}A|\le\varepsilon\sqrt{n!}\prod_i\sigma_i\right)\le\min\left\{1,\left(\frac{2\pi e}{\beta}\right)^{\beta/2}\kappa_{n,\beta}\varepsilon^\beta\right\}.$$
--   This is a comparison at the exact second-moment scale for non-Gaussian independent rows, with no coordinate independence or common-law requirement.
--
--   **Formalization Note** Covariance entry $(j,l)$ is $E(\overline{R_{i,j}}R_{i,l})$; its integrability is part of the finite covariance equality. The projection denominator is used only for nonzero $c$.
--
--   Differences from the source:
--
--   - encoding: K ∈ {ℝ,ℂ,ℍ} and β = dim_ℝ K → published Scalar carriers and beta; reason: the three concrete fields and real-coordinate normalizations are identical
--   - encoding: independent random inputs → coordinate functions under their probability product laws; reason: these are exactly the joint laws of independent Borel random variables; no moment or density restriction is added
--   - encoding: Laplace comparison for s ≥ 0 → published LaplaceOrder for s > 0; reason: at s = 0 both bounded integrands equal 1 under probability laws
--   - encoding: the finite covariance matrix ER_i*R_i = σ_i² I → entrywise Integrable conjugate products and their Bochner integrals equal σ_i² δ_jl; reason: finite diagonal second moments imply all cross products are integrable by Cauchy–Schwarz; this excludes the Bochner default value without adding a moment assumption
--   - generalization: the labelled Theorem C.1 gives (37) and (38) → also Integrable |per A|² and its exact expectation n! ∏ σ_i²; reason: the paragraph immediately following (38), p.19, states this identity; it is expressly required by the supplement brief and dropping it leaves the full labelled theorem
-- source:
--   Frederic Koehler, Pui Kuen Leung, STOC 2027 submission #977 (October 2026), Theorem C.1, p.19 (PDF SHA256 e25737f1d5e3492905f8eeaa41d92c55d95f73622a3b5846cc87aac6a346d4ec)

import Mathlib
import Definitions.Def_GinibrePermanent977_Anticoncentration_Supplement_Model
open MeasureTheory ProbabilityTheory
open scoped BigOperators Nat ENNReal

namespace GinibrePermanent977.Anticoncentration.Supplement

/-- Theorem C.1 (36)–(38), p.19, including the exact finite second moment stated after (38).
Each μ_i is a row law, with arbitrary coordinate dependence; their product is the matrix law. -/
theorem theorem_C_1 (F : Scalar) (n : ℕ) (hn : 1 ≤ n)
    (μ : Fin n → Measure (Fin n → F.K)) [∀ i, IsProbabilityMeasure (μ i)]
    (σ : Fin n → ℝ) (hσ : ∀ i, 0 < σ i)
    (hiso : ∀ i, RowIsotropic (μ i) (σ i))
    (hproj : ∀ i (c : Fin n → F.K), c ≠ 0 →
      StochasticOrders.LaplaceTransform.LaplaceOrder (gammaLaw F 1) (μ i)
        id (fun r => ‖rowAction r c‖ ^ 2 / (σ i ^ 2 * norm2 c ^ 2))) :
    StochasticOrders.LaplaceTransform.LaplaceOrder (ginibre F n n) (ginibre F n n)
      (deltaPower F) (fun G => ‖normPer G‖ ^ 2) ∧
    StochasticOrders.LaplaceTransform.LaplaceOrder (ginibre F n n) (Measure.pi μ)
      (fun G => ‖normPer G‖ ^ 2)
      (fun A => ‖perK A‖ ^ 2 / ((n ! : ℝ) * ∏ i, σ i ^ 2)) ∧
    Integrable (fun A => ‖perK A‖ ^ 2) (Measure.pi μ) ∧
    (∫ A, ‖perK A‖ ^ 2 ∂Measure.pi μ) = (n ! : ℝ) * ∏ i, σ i ^ 2 ∧
    ∀ ε : ℝ, 0 < ε →
      (Measure.pi μ) {A | ‖perK A‖ ≤ ε * Real.sqrt (n ! : ℝ) * ∏ i, σ i} ≤
        ENNReal.ofReal (min 1 (((2 * Real.pi * Real.exp 1) / (F.beta : ℝ)) ^
          ((F.beta : ℝ) / 2) * kappa F n * ε ^ F.beta)) := by sorry

end GinibrePermanent977.Anticoncentration.Supplement
