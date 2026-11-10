-- Prove2me | Theorems.Thm_GinibrePermanent977_Anticoncentration_lemma_3_8_kappa_asymptotics
-- name    : GinibrePermanent977.Anticoncentration.lemma_3_8_kappa_asymptotics
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:10:29.432557+00:00
-- url     : https://prove2.me/theorems/78b7923d-839e-484b-a537-59c428924683
-- title:
--   Lemma 3.8 — asymptotics of the density constant $\kappa_{n,\beta}$
-- statement:
--   For $\beta\in\{1,2,4\}$ and $n\ge1$ let
--
--   $$
--   \kappa_{n,\beta}=\lim_{s\to\infty}\Bigl(\frac s\pi\Bigr)^{\beta/2}E\,e^{-s\Delta_n^{\mathbb K}}=\frac{(n!)^{\beta/2}}{\pi^{\beta/2}}\Bigl(\frac\beta2\Bigr)^{\beta n/2}\frac{\Gamma(\beta/2)}{\Gamma(\beta n/2)}
--   $$
--
--   (Eqs. (20), (22)). Then, as $n\to\infty$,
--
--   $$
--   \kappa_{n,\beta}\asymp_\beta n^{(\beta+2)/4},
--   $$
--
--   that is, there are constants $0<c_\beta\le C_\beta$ and $N_\beta$ with $c_\beta n^{(\beta+2)/4}\le\kappa_{n,\beta}\le C_\beta n^{(\beta+2)/4}$ for $n\ge N_\beta$.
--
--   This converts the exact density bound $p_n^{\mathbb K}(0)\le\kappa_{n,\beta}$ into the polynomial bound of Theorem 1.1.
--
--   **Formalization Note** $\asymp$ is Mathlib's `IsTheta` along `atTop` for functions of $n\in\mathbb N$.
--
--   Differences from the source:
--
--   - encoding: $K\in\{\mathbb R,\mathbb C,\mathbb H\}$ → a tag `F : Scalar` with carriers ℝ, ℂ, ℍ[ℝ] and β = 1, 2, 4; reason: Lean convention selecting the three concrete scalar domains; same instances
--   - encoding: $\kappa_{n,\beta}$ defined as the limit (20) → `kappa F n` = the closed form (22); reason: (20) = (22) is computed on p. 12; same number for every $n\ge1$
--   - encoding: $\asymp_\beta$ → `=Θ[atTop]`; reason: the meaning of the two-sided asymptotic comparison
-- source:
--   Frederic Koehler, Pui Kuen Leung, STOC 2027 submission #977 (October 2026), §3.5, p. 12, Lemma 3.8, Eq. (21); Eqs. (20), (22) (PDF SHA-256 e25737f1d5e3492905f8eeaa41d92c55d95f73622a3b5846cc87aac6a346d4ec)

import Mathlib
import Definitions.Def_StochasticOrders_LaplaceTransform_LaplaceOrder
import Definitions.Def_GinibrePermanent977_Anticoncentration_Model
open MeasureTheory ProbabilityTheory Matrix
open scoped ComplexOrder Nat ENNReal

namespace GinibrePermanent977.Anticoncentration

/-- Lemma 3.8, p. 12. `κ_{n,β} ≍_β n^{(β+2)/4}` as `n → ∞`, for each `K ∈ {ℝ, ℂ, ℍ}`: there are
constants `0 < c ≤ C` depending only on `β` with `c n^{(β+2)/4} ≤ κ_{n,β} ≤ C n^{(β+2)/4}` for all
large `n` (Mathlib's `IsTheta` along `atTop`). -/
theorem lemma_3_8_kappa_asymptotics (F : Scalar) :
    (fun n : ℕ => kappa F n) =Θ[Filter.atTop]
      (fun n : ℕ => (n : ℝ) ^ (((F.beta : ℝ) + 2) / 4)) := by sorry

end GinibrePermanent977.Anticoncentration
