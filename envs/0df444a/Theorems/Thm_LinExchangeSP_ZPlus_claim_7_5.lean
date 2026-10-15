-- Prove2me | Theorems.Thm_LinExchangeSP_ZPlus_claim_7_5
-- name    : LinExchangeSP.ZPlus.claim_7_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:45:28.564783+00:00
-- url     : https://prove2.me/theorems/556a5e3b-363d-4655-ad9c-9a136bc63d8e
-- title:
--   Claim 7.5, p. 23 — κ(i)Mᵢq ≤ Bγᵢ for i ∈ T₂ and q = q⁽ⁱ⁾
-- statement:
--   Let $M \in \mathcal{Z}_+(t,t)$, $t \ge 1$, have all diagonal entries positive, let $\gamma \in \mathbb{Q}^t$ with $\gamma > 0$, and let $B = \sum_{j=1}^t\gamma_j/\min_{i\in[t]}\gamma_i$. Let $i \in T_2$, let $\kappa(i)$ be as in Lemma 7.4(iii), and let $q = q^{(i)}$ be the vector of Lemma 7.4(i): $q \ge 0$, $M_\ell q = 0$ for $\ell \in D_i\setminus\{i\}$, $q_i = 1$, $q_\ell = 0$ for $\ell \notin D_i$. Then
--
--   $$\kappa(i)\, M_i q \ \le\ B\gamma_i.$$
--
--   Combined with $M_i\bar p \le B\kappa(i)M_iq$ (18), it completes the bound $M_i\bar p \le B^2\gamma_i$ for $i \in T_2$ in the proof of Theorem 6.4.
--
--   **Formalization Note** The statement quantifies over every $q$ with the four properties of Lemma 7.4(i); by that lemma there is exactly one, $q^{(i)}$. $\kappa(i)$ is the intrinsic form described for Lemma 7.4(iii). $\gamma > 0$ and the positive diagonal are the standing assumptions of §7; $t \ge 1$ is needed for $B$.
-- source:
--   Garg & Végh, A strongly polynomial algorithm for linear exchange markets, arXiv:1809.06266v3, p. 23, Claim 7.5 (context p. 22)

import Mathlib
import Definitions.Def_LinExchangeSP_ZPlus_Setting
import Definitions.Def_LinExchangeSP_ZPlus_Construction

namespace LinExchangeSP.ZPlus

/-- Claim 7.5 (p. 23), in the setting of §7 with `γ > 0`: for `i ∈ T₂` and `q = q^(i)` of
Lemma 7.4(i), `κ(i) M_i q ≤ B γ_i`, `B = ∑ⱼ γⱼ / minᵢ γᵢ`. -/
theorem claim_7_5 {t : ℕ} (ht : 0 < t) (M : Matrix (Fin t) (Fin t) ℚ) (hM : IsZPlus M)
    (hdiag : ∀ i, 0 < M i i) (γ : Fin t → ℚ) (hγ : ∀ i, 0 < γ i) (i : Fin t) (hi : InT2 M i)
    (q : Fin t → ℝ) (hq0 : ∀ l, 0 ≤ q l) (hqD : ∀ l ∈ D M i, l ≠ i → rowVal M q l = 0)
    (hqi : q i = 1) (hqout : ∀ l, l ∉ D M i → q l = 0) :
    kappa M γ i * rowVal M q i ≤ Bconst γ ht * (γ i : ℝ) := by sorry

end LinExchangeSP.ZPlus
