-- Prove2me | Theorems.Thm_GinibrePermanent977_Anticoncentration_proposition_3_5_fourier_compression
-- name    : GinibrePermanent977.Anticoncentration.proposition_3_5_fourier_compression
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:10:19.839962+00:00
-- url     : https://prove2.me/theorems/c656a649-f58e-48e3-bdcc-effa0efbd2ed
-- title:
--   Proposition 3.5 — Fourier coordinate compression of permanental cofactors
-- statement:
--   Throughout, $\mathbb K\in\{\mathbb R,\mathbb C,\mathbb H\}$ with $\beta=\dim_{\mathbb R}\mathbb K\in\{1,2,4\}$; a **standard $\mathbb K$-Gaussian** has independent real coordinates $N(0,1/\beta)$, $G_n^{\mathbb K}$ is an $n\times n$ matrix and $B_n$ an $(n-1)\times n$ matrix of i.i.d. standard $\mathbb K$-Gaussian entries, $\operatorname{per}_{\mathbb K}A=\sum_{\sigma}a_{1\sigma(1)}a_{2\sigma(2)}\cdots a_{n\sigma(n)}$ is the row-ordered permanent, and $(C_n^{\mathbb K})_j=\operatorname{per}_{\mathbb K}((B_n)_{-j})$ is the permanental cofactor column ($C_1^{\mathbb K}=(1)$).
--
--   Let $n\ge2$, $C=C_n^{\mathbb K}$ and
--
--   $$
--   \varphi_n^{\mathbb K}(z)=E\,e^{i(z,C)_{\mathbb R}}=E\exp\Bigl(i\operatorname{Re}\sum_{j=1}^n\bar z_jC_j\Bigr),\qquad z\in\mathbb K^n.
--   $$
--
--   Then for every $z\in\mathbb K^n$, $\varphi_n^{\mathbb K}(z)$ is real and
--
--   $$
--   0\le\varphi_n^{\mathbb K}(z)\le\varphi_n^{\mathbb K}(\|z\|_2e_1).
--   $$
--
--   No test direction concentrates the cofactor column more than a single coordinate. The restriction $n\ge2$ is needed: $C_1=(1)$ has characteristic function $e^{i\operatorname{Re}z}$.
--
--   Differences from the source:
--
--   - encoding: $K\in\{\mathbb R,\mathbb C,\mathbb H\}$ → a tag `F : Scalar` with carriers ℝ, ℂ, ℍ[ℝ] and β = 1, 2, 4; reason: Lean convention selecting the three concrete scalar domains; same instances
--   - encoding: 1-based indices $j=1,\dots,n$, $e_1$ → 0-based `Fin n` indices, $e_1$ = `Pi.single 0`; reason: Lean convention; source index j is Lean index j−1
--   - encoding: random variables (independent Gaussian/gamma variables) → functions on the canonical product sample spaces `ginibre`, `gammaVec`, `benchLaw`; reason: independence is encoded by product measures; same laws
--   - encoding: “$0\le\varphi\le\psi$” for characteristic functions → the order of ℂ (`ComplexOrder`): both sides real and ordered; reason: the source asserts that these values are real; same statement
-- source:
--   Frederic Koehler, Pui Kuen Leung, STOC 2027 submission #977 (October 2026), §3.2, p. 9, Proposition 3.5, Eq. (13) (PDF SHA-256 e25737f1d5e3492905f8eeaa41d92c55d95f73622a3b5846cc87aac6a346d4ec)

import Mathlib
import Definitions.Def_StochasticOrders_LaplaceTransform_LaplaceOrder
import Definitions.Def_GinibrePermanent977_Anticoncentration_Model
open MeasureTheory ProbabilityTheory Matrix
open scoped ComplexOrder Nat ENNReal

namespace GinibrePermanent977.Anticoncentration

/-- Proposition 3.5 (Fourier coordinate compression), p. 9. Let `K ∈ {ℝ, ℂ, ℍ}`, `n ≥ 2`, `B` an
`(n-1) × n` standard `K`-Gaussian matrix with permanental cofactor column `C = C_n^K`, and
`φ_n^K(z) = E exp(i (z, C)_ℝ) = E exp(i Re ∑_j \bar z_j C_j)`. For every `z ∈ K^n`,
`0 ≤ φ_n^K(z) ≤ φ_n^K(‖z‖₂ e₁)` (in the order of `ℂ`: both values are real). `e₁` is the first
standard basis vector (Lean index `0`). -/
theorem proposition_3_5_fourier_compression (F : Scalar) {n : ℕ} (hn : 2 ≤ n)
    (z : Fin n → F.K) :
    0 ≤ charFunK (ginibre F (n - 1) n) perCofactor z ∧
      charFunK (ginibre F (n - 1) n) perCofactor z ≤
        charFunK (ginibre F (n - 1) n) perCofactor
          (Pi.single (⟨0, by omega⟩ : Fin n) (norm2 z • (1 : F.K))) := by sorry

end GinibrePermanent977.Anticoncentration
