-- Prove2me | Theorems.Thm_GinibrePermanent977_Anticoncentration_theorem_3_6_scalar_cofactor_laplace
-- name    : GinibrePermanent977.Anticoncentration.theorem_3_6_scalar_cofactor_laplace
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T00:44:23.32944+00:00
-- url     : https://prove2.me/theorems/e5e122bf-7cab-4bfc-b06c-cc3dbf7a6b21
-- title:
--   Theorem 3.6 (16): scalar cofactor Laplace comparison
-- statement:
--   Fix $\mathbb K\in\{\mathbb R,\mathbb C,\mathbb H\}$ and let $\beta=\dim_{\mathbb R}\mathbb K$. Let $n\ge1$ and let $C_n^{\mathbb K}$ be the permanental cofactor column of a standard $(n-1)\times n$ Ginibre matrix, with each permanent product taken in increasing row order. For independent gamma variables $\gamma_{k,\beta}\sim\mathrm{Gamma}(\beta k/2,2/\beta)$ in shape-scale convention, put $\Pi_{n,\beta}=\prod_{k=2}^{n}\gamma_{k,\beta}$, with the empty product equal to one. Then
--
--   $$
--   \Pi_{n,\beta}\le_{Lt}\|C_n^{\mathbb K}\|_2^2.
--   $$
--
--   Thus for every $s>0$, the Laplace transform of the squared cofactor norm is at most that of the gamma product. This is equation (16), the scalar assertion of Theorem 3.6, and supplies the inverse-moment comparison used in the density bound.
-- source:
--   F. Koehler and P. K. Leung, Anticoncentration of the Permanent in Ginibre Ensembles, STOC 2027 submission 977, October 2026, p.10, Theorem 3.6, equation (16); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/977.pdf

import Mathlib
import Definitions.Def_GinibrePermanent977_Anticoncentration_Model
open MeasureTheory ProbabilityTheory Matrix
open GinibrePermanent977.Anticoncentration

theorem GinibrePermanent977.Anticoncentration.theorem_3_6_scalar_cofactor_laplace (F : Scalar) (n : ℕ) (hn : 1 ≤ n) :
    StochasticOrders.LaplaceTransform.LaplaceOrder (gammaVec F n) (ginibre F (n-1) n)
      gammaPi (fun B => norm2 (perCofactor (n := n) B)^2) := by sorry
