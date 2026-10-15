-- Prove2me | Theorems.Thm_LinExchangeSP_ZPlus_lemma_7_4_iii
-- name    : LinExchangeSP.ZPlus.lemma_7_4_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:45:33.103673+00:00
-- url     : https://prove2.me/theorems/86adc9a0-3c18-4e3e-a086-d0b34c972edb
-- title:
--   Lemma 7.4(iii), p. 21 — for i ∈ T₂ there is r⁽ⁱ⁾ ≥ 0 with Mr⁽ⁱ⁾ ≤ γ, M_ℓr⁽ⁱ⁾ = γ_ℓ on Dᵢ and r⁽ⁱ⁾ᵢ = κ(i)
-- statement:
--   Let $M \in \mathcal{Z}_+(t,t)$ have all diagonal entries positive, let $\gamma \in \mathbb{Q}^t$ with $\gamma > 0$, and let $D_i$ and $T_2$ be as in §7.2. For $i \in T_2$ let $\kappa(i)$ be the $i$-th entry of $(M_{D_i,D_i})^{-1}\gamma_{D_i}$. If $i \in T_2$, there is a vector $r^{(i)} \in \mathbb{R}^t_+$ with
--
--   $$Mr^{(i)} \le \gamma,\qquad M_\ell r^{(i)} = \gamma_\ell \ \ (\ell \in D_i),\qquad r^{(i)}_i = \kappa(i).$$
--
--   The point $r^{(i)}$ certifies that the extra constraint $\bar p_i \le \kappa(i)$ of the approximating system is tight on $P_M$, and it gives the bound $\eta_i \le \kappa(i) M_i q^{(i)}$ in the case $i \in T_2$ of the proof of Theorem 6.4.
--
--   **Formalization Note** The paper defines $\kappa(i) := Y^{(ij)}_d\gamma^{(ij)}$ in (12) through the elimination for an arbitrary arc $ij$, and shows inside this proof that $\hat r_d = \kappa(i)$; here $\kappa(i)$ is stated intrinsically as that same number, the $i$-th entry of the unique solution of $M_\ell r = \gamma_\ell$ ($\ell \in D_i$) supported on $D_i$ (a disclosed restatement; on the example of p. 20 both give $\kappa(1) = 59/15$). $M_{D_i,D_i}$ is invertible because $i \in T_2$. $\gamma > 0$ and the positive diagonal are the standing assumptions of §7.
-- source:
--   Garg & Végh, A strongly polynomial algorithm for linear exchange markets, arXiv:1809.06266v3, p. 21, Lemma 7.4(iii); κ(i) from (12), p. 19

import Mathlib
import Definitions.Def_LinExchangeSP_ZPlus_Setting
import Definitions.Def_LinExchangeSP_ZPlus_Construction

namespace LinExchangeSP.ZPlus

/-- Lemma 7.4(iii) (p. 21), in the setting of §7 with `γ > 0`: if `i ∈ T₂`, there is `r ∈ ℝᵗ₊` with
`Mr ≤ γ`, `M_ℓ r = γ_ℓ` for all `ℓ ∈ Dᵢ`, and `r_i = κ(i)`, where `κ(i)` is stated intrinsically
as the `i`-th entry of `(M_{Dᵢ,Dᵢ})⁻¹ γ_{Dᵢ}`. -/
theorem lemma_7_4_iii {t : ℕ} (M : Matrix (Fin t) (Fin t) ℚ) (hM : IsZPlus M)
    (hdiag : ∀ i, 0 < M i i) (γ : Fin t → ℚ) (hγ : ∀ i, 0 < γ i) (i : Fin t) (hi : InT2 M i) :
    ∃ r : Fin t → ℝ, (∀ l, 0 ≤ r l) ∧ (∀ l, rowVal M r l ≤ (γ l : ℝ)) ∧
      (∀ l ∈ D M i, rowVal M r l = (γ l : ℝ)) ∧ r i = kappa M γ i := by sorry

end LinExchangeSP.ZPlus
