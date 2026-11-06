-- Prove2me | Theorems.Thm_HananyPuder_tendsto_uniformExp_prod_xi_pow_sub_uniformExp
-- name    : HananyPuder.tendsto_uniformExp_prod_xi_pow_sub_uniformExp
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-05T22:12:42.699649+00:00
-- url     : https://prove2.me/theorems/4c2eec6b-681c-4dc4-b920-aef8831011ac
-- title:
--   Hanany–Puder, Theorem 1.3 — for a non-power v, E_{vᵏ}[ξ₁^α₁⋯ξ_r^α_r] − E_unif[ξ_k^α₁⋯ξ_{rk}^α_r] → 0
-- statement:
--   Let $v \in \mathbf F_d$ be a non-power (`IsNonPower`: $v \ne e$ and $v$ is not $u^m$ for any $u$ and $m \ge 2$), let $k \ge 1$, and let $\alpha_1, \dots, \alpha_r \ge 0$. Then
--   $$\lim_{N\to\infty}\Big(\mathbf E_{v^k,N}[\xi_1^{\alpha_1} \cdots \xi_r^{\alpha_r}] - \mathbf E_{\mathrm{unif},N}[\xi_k^{\alpha_1} \xi_{2k}^{\alpha_2} \cdots \xi_{rk}^{\alpha_r}]\Big) = 0.$$
--   Here $\mathbf E_{v^k,N}$ is the expectation over i.i.d. uniform $\sigma_1, \dots, \sigma_d \in \mathbf S_N$ of a function of $v^k(\sigma_1, \dots, \sigma_d)$ (`FreeGroup.lift σ (v ^ k)`), $\mathbf E_{\mathrm{unif},N}$ is the expectation over a uniform $\sigma \in \mathbf S_N$, and $\xi_i(\sigma)$ (`xi`) is the number of fixed points of $\sigma^i$.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 31, the theorem of Hanany–Puder cited in the proof of Lemma 10.2, which cites Hanany, L. and Puder, D., Word measures on symmetric groups, Int. Math. Res. Not. IMRN 2023 (2023) 9221–9297, https://doi.org/10.1093/imrn/rnac084 (arXiv:2009.00897v4), Theorem 1.3

import Mathlib
import Definitions.Def_StrongConv

open Filter Topology StrongConv

namespace HananyPuder

theorem tendsto_uniformExp_prod_xi_pow_sub_uniformExp {d r : ℕ} (v : FreeGroup (Fin d))
    (hv : IsNonPower v) (k : ℕ) (hk : 1 ≤ k) (α : Fin r → ℕ) :
    Tendsto (fun N : ℕ =>
        uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
            ∏ i : Fin r, ((xi ((i : ℕ) + 1) (FreeGroup.lift σ (v ^ k)) : ℕ) : ℝ) ^ α i) -
          uniformExp (fun σ : Equiv.Perm (Fin N) =>
            ∏ i : Fin r, ((xi (((i : ℕ) + 1) * k) σ : ℕ) : ℝ) ^ α i))
      atTop (𝓝 0) := by
  sorry

end HananyPuder
