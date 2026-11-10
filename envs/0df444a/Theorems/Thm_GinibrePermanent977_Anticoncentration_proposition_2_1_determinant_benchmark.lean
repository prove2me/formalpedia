-- Prove2me | Theorems.Thm_GinibrePermanent977_Anticoncentration_proposition_2_1_determinant_benchmark
-- name    : GinibrePermanent977.Anticoncentration.proposition_2_1_determinant_benchmark
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:10:22.041757+00:00
-- url     : https://prove2.me/theorems/3f3899cf-b65b-44ef-9430-50fca043f3cc
-- title:
--   Proposition 2.1 — Gaussian determinant benchmark
-- statement:
--   Let $\mathbb F\in\{\mathbb R,\mathbb C\}$, $\beta=\dim_{\mathbb R}\mathbb F$, and let $\gamma_{k,\beta}\sim\mathrm{Gamma}(\beta k/2,2/\beta)$ (shape, scale) be independent, $\Pi_{m,\beta}=\prod_{k=2}^m\gamma_{k,\beta}$. Let $B_n$ be an $(n-1)\times n$ standard $\mathbb F$-Gaussian matrix and $(C_n^{\det})_j=(-1)^{j-1}\det((B_n)_{-j})$ its signed determinantal cofactor column. For $n\ge2$, with $g_n$ a standard $\mathbb F$-Gaussian column independent of $\Pi_{n-1,\beta}$,
--
--   $$
--   C_n^{\det}\overset d=\sqrt{\Pi_{n-1,\beta}}\,g_n\quad(7),\qquad
--   C_n^{\det}(C_n^{\det})^*\overset d=\Pi_{n-1,\beta}\,g_ng_n^*\quad(8),\qquad
--   \|C_n^{\det}\|_2^2\overset d=\Pi_{n,\beta}\quad(9).
--   $$
--
--   Moreover, for every $n\ge1$, with $G_n$ a standard $\mathbb F$-Ginibre matrix,
--
--   $$
--   \Delta_n=\frac{|\det G_n|^2}{n!}\overset d=\prod_{k=1}^n\frac{\gamma_{k,\beta}}{k}\quad(10).
--   $$
--
--   These are the exact determinantal laws that the permanent comparison imitates one-sidedly.
--
--   Differences from the source:
--
--   - encoding: $\mathbb F\in\{\mathbb R,\mathbb C\}$ → a tag `F : Scalar` with `F ≠ quaternion`; reason: Lean convention; same two fields
--   - encoding: 1-based indices $j=1,\dots,n$, $e_1$ → 0-based `Fin n` indices, $e_1$ = `Pi.single 0`; reason: Lean convention; source index j is Lean index j−1
--   - encoding: random variables (independent Gaussian/gamma variables) → functions on the canonical product sample spaces `ginibre`, `gammaVec`, `benchLaw`; reason: independence is encoded by product measures; same laws
--   - encoding: $=_d$ → `IdentDistrib` (equal laws, both maps a.e. measurable); reason: the compared maps use polynomial operations, norms and measurable real roots; measurability adds no hypothesis and the laws are unchanged
--   - encoding: $\det$ over $\mathbb R,\mathbb C$ → `cdetK` (Leibniz sum with row-ordered products); reason: equals the determinant over a commutative field
-- source:
--   Frederic Koehler, Pui Kuen Leung, STOC 2027 submission #977 (October 2026), §2, p. 4, Proposition 2.1, Eqs. (7)–(10) (cofactor columns, p. 3) (PDF SHA-256 e25737f1d5e3492905f8eeaa41d92c55d95f73622a3b5846cc87aac6a346d4ec)

import Mathlib
import Definitions.Def_StochasticOrders_LaplaceTransform_LaplaceOrder
import Definitions.Def_GinibrePermanent977_Anticoncentration_Model
open MeasureTheory ProbabilityTheory Matrix
open scoped ComplexOrder Nat ENNReal

namespace GinibrePermanent977.Anticoncentration

/-- Proposition 2.1 (Gaussian determinant benchmark), p. 4. Let `F ∈ {ℝ, ℂ}` and `β = dim_ℝ F`. For
`n ≥ 2`, with `g_n` a standard `F`-Gaussian column independent of `Π_{n-1,β}`:
(7) `C_n^{det} =_d √Π_{n-1,β} g_n`; (8) `C_n^{det}(C_n^{det})^* =_d Π_{n-1,β} g_n g_n^*`;
(9) `‖C_n^{det}‖₂² =_d Π_{n,β}`. Moreover, for every `n ≥ 1`,
(10) `Δ_n = |det G_n|²/n! =_d ∏_{k=1}^n γ_{k,β}/k`. -/
theorem proposition_2_1_determinant_benchmark (F : Scalar) (hF : F ≠ Scalar.quaternion) :
    (∀ n : ℕ, 2 ≤ n →
      IdentDistrib detCofactor benchVec (ginibre F (n - 1) n) (benchLaw F n) ∧
      IdentDistrib (fun B => fun i j => detCofactor B i * star (detCofactor B j))
        (fun p => fun i j => benchVec p i * star (benchVec p j))
        (ginibre F (n - 1) n) (benchLaw F n) ∧
      IdentDistrib (fun B => norm2 (detCofactor B) ^ 2) gammaPi
        (ginibre F (n - 1) n) (gammaVec F n)) ∧
    ∀ n : ℕ, 1 ≤ n →
      IdentDistrib (fun G : Fin n → Fin n → F.K => ‖cdetK G‖ ^ 2 / (n ! : ℝ))
        (fun γ : Fin n → ℝ => ∏ k, γ k / ((k : ℕ) + 1 : ℝ))
        (ginibre F n n) (gammaVec F n) := by sorry

end GinibrePermanent977.Anticoncentration
