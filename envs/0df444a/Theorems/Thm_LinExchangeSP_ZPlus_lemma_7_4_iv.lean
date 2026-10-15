-- Prove2me | Theorems.Thm_LinExchangeSP_ZPlus_lemma_7_4_iv
-- name    : LinExchangeSP.ZPlus.lemma_7_4_iv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:45:42.466909+00:00
-- url     : https://prove2.me/theorems/40102f42-ba22-4aa5-810e-31a2394bb19a
-- title:
--   Lemma 7.4(iv), p. 21 — for i ∈ T₃ there is r⁽ⁱ⁾ ≥ 0 with Mr⁽ⁱ⁾ ≤ γ and M_ℓr⁽ⁱ⁾ = γ_ℓ for ℓ ∈ Dᵢ ∖ {i}
-- statement:
--   Let $M \in \mathcal{Z}_+(t,t)$ have all diagonal entries positive, let $\gamma \in \mathbb{Q}^t$ with $\gamma > 0$, and let $D_i$ and $T_3$ be as in §7.2. If $i \in T_3$, there is a vector $r^{(i)} \in \mathbb{R}^t_+$ with
--
--   $$Mr^{(i)} \le \gamma,\qquad M_\ell r^{(i)} = \gamma_\ell \ \ (\ell \in D_i\setminus\{i\}).$$
--
--   It is the point of $P_M$ used, in the case $i \in T_3$ of the proof of Theorem 6.4, to bound the right-hand side $\eta_i$ by $\lambda_i$.
--
--   **Formalization Note** $\gamma > 0$ and the positive diagonal are the standing assumptions of §7 (p. 16).
-- source:
--   Garg & Végh, A strongly polynomial algorithm for linear exchange markets, arXiv:1809.06266v3, p. 21, Lemma 7.4(iv)

import Mathlib
import Definitions.Def_LinExchangeSP_ZPlus_Setting
import Definitions.Def_LinExchangeSP_ZPlus_Construction

namespace LinExchangeSP.ZPlus

/-- Lemma 7.4(iv) (p. 21), in the setting of §7 with `γ > 0`: if `i ∈ T₃`, there is `r ∈ ℝᵗ₊` with
`Mr ≤ γ` and `M_ℓ r = γ_ℓ` for all `ℓ ∈ Dᵢ \ {i}`. -/
theorem lemma_7_4_iv {t : ℕ} (M : Matrix (Fin t) (Fin t) ℚ) (hM : IsZPlus M)
    (hdiag : ∀ i, 0 < M i i) (γ : Fin t → ℚ) (hγ : ∀ i, 0 < γ i) (i : Fin t) (hi : InT3 M i) :
    ∃ r : Fin t → ℝ, (∀ l, 0 ≤ r l) ∧ (∀ l, rowVal M r l ≤ (γ l : ℝ)) ∧
      ∀ l ∈ D M i, l ≠ i → rowVal M r l = (γ l : ℝ) := by sorry

end LinExchangeSP.ZPlus
