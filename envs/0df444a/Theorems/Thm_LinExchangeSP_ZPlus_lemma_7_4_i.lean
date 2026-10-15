-- Prove2me | Theorems.Thm_LinExchangeSP_ZPlus_lemma_7_4_i
-- name    : LinExchangeSP.ZPlus.lemma_7_4_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:45:24.641894+00:00
-- url     : https://prove2.me/theorems/cda287dd-d02d-4058-a01e-7c997204ade2
-- title:
--   Lemma 7.4(i), p. 21 — for i ∈ T₂ ∪ T₃ there is a unique q⁽ⁱ⁾ ≥ 0 supported on Dᵢ with M_ℓq⁽ⁱ⁾ = 0 (ℓ ∈ Dᵢ ∖ {i}), q⁽ⁱ⁾ᵢ = 1
-- statement:
--   Let $M \in \mathcal{Z}_+(t,t)$ have all diagonal entries positive, with digraph $H$, reachable sets $D_i$ and partition $T_1, T_2, T_3$ as in §7.2. For every $i \in T_2 \cup T_3$ there is a unique vector $q^{(i)} \in \mathbb{R}^t_+$ such that
--
--   $$M_\ell q^{(i)} = 0 \ \ (\ell \in D_i\setminus\{i\}),\qquad q^{(i)}_i = 1,\qquad q^{(i)}_\ell = 0 \ \ (\ell \in [t]\setminus D_i).$$
--
--   The vector $q^{(i)}$ describes the coefficients of the two-variable constraints $\bar p_j - q^{(i)}_j\bar p_i \ge \delta^{(ij)}$ of the approximating system, and enters Claim 7.5.
--
--   **Formalization Note** Uniqueness is within $\mathbb{R}^t_+$, as printed. The positive diagonal is the standing assumption of §7.
-- source:
--   Garg & Végh, A strongly polynomial algorithm for linear exchange markets, arXiv:1809.06266v3, p. 21, Lemma 7.4(i)

import Mathlib
import Definitions.Def_LinExchangeSP_ZPlus_Setting
import Definitions.Def_LinExchangeSP_ZPlus_Construction

namespace LinExchangeSP.ZPlus

/-- Lemma 7.4(i) (p. 21), in the setting of §7: for `i ∈ T₂ ∪ T₃` there is a unique `q ∈ ℝᵗ₊` with
`M_ℓ q = 0` for `ℓ ∈ Dᵢ \ {i}`, `q_i = 1` and `q_ℓ = 0` for `ℓ ∉ Dᵢ`. -/
theorem lemma_7_4_i {t : ℕ} (M : Matrix (Fin t) (Fin t) ℚ) (hM : IsZPlus M)
    (hdiag : ∀ i, 0 < M i i) (i : Fin t) (hi : InT2 M i ∨ InT3 M i) :
    ∃! q : Fin t → ℝ, (∀ l, 0 ≤ q l) ∧ (∀ l ∈ D M i, l ≠ i → rowVal M q l = 0) ∧
      q i = 1 ∧ ∀ l, l ∉ D M i → q l = 0 := by sorry

end LinExchangeSP.ZPlus
