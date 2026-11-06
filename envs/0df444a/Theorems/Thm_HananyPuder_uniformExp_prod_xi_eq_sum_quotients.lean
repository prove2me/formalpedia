-- Prove2me | Theorems.Thm_HananyPuder_uniformExp_prod_xi_eq_sum_quotients
-- name    : HananyPuder.uniformExp_prod_xi_eq_sum_quotients
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T22:12:56.257234+00:00
-- url     : https://prove2.me/theorems/314cce8a-86a7-40dc-8343-2fd5419b1baa
-- title:
--   Hanany–Puder, Example 3.6, Definition 6.6 and Proposition 6.8 — E_w[ξ₁^α₁⋯ξ_r^α_r] as a sum over the quotients of Γ^w_α (CGTvH (10.2))
-- statement:
--   Let $w \ne 1$ be an element of the free group $\mathbf F_d$ with cyclic reduction $L$, and let $\alpha_1, \dots, \alpha_r \ge 0$ with $\alpha_1 + \dots + \alpha_r \ge 1$. Let $\Gamma^w_\alpha$ be the graph made of $\alpha_1$ disjoint cycles depicting $w$, $\alpha_2$ disjoint cycles depicting $w^2$, and so on, with edges labeled by $\{1, \dots, d\}$ (vertices `CycleVert L α`). For a partition $\Gamma$ of its vertices that gives a quotient graph without folding (`IsFoldFree`), let $v_\Gamma$ be the number of blocks (`quotVert`), $e^j_\Gamma$ the number of edges labeled $j$ of the quotient graph (`quotEdge`), and $e_\Gamma = e^1_\Gamma + \dots + e^d_\Gamma$. If $N \ge e^j_\Gamma$ for every such $\Gamma$ and every $j$, then
--   $$\mathbf E_{w,N}[\xi_1^{\alpha_1} \cdots \xi_r^{\alpha_r}] = \sum_\Gamma \frac{(\frac1N)^{e_\Gamma - v_\Gamma} \prod_{i=1}^{v_\Gamma - 1}(1 - \frac iN)}{\prod_{j=1}^d \prod_{i=1}^{e^j_\Gamma - 1}(1 - \frac iN)},$$
--   the sum over the fold-free partitions $\Gamma$. Here $\mathbf E_{w,N}$ is the expectation over i.i.d. uniform $\sigma_1, \dots, \sigma_d \in \mathbf S_N$ of a function of $w(\sigma_1, \dots, \sigma_d)$ (`FreeGroup.lift σ w`), and $\xi_i(\sigma)$ (`xi`) is the number of fixed points of $\sigma^i$.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 30, the formula of Hanany–Puder cited in the proof of Lemma 10.1, which cites Hanany, L. and Puder, D., Word measures on symmetric groups, Int. Math. Res. Not. IMRN 2023 (2023) 9221–9297, https://doi.org/10.1093/imrn/rnac084 (arXiv:2009.00897v4), Example 3.6, Definition 6.6 and Proposition 6.8

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_StrongConvG4

open StrongConv

namespace HananyPuder

theorem uniformExp_prod_xi_eq_sum_quotients {d r : ℕ} (w : FreeGroup (Fin d)) (hw : w ≠ 1)
    (α : Fin r → ℕ) (hα : 0 < ∑ i, α i) (N : ℕ)
    (hN : ∀ P : Finpartition (Finset.univ :
        Finset (CycleVert (FreeGroup.reduceCyclically w.toWord) α)),
      IsFoldFree P → ∀ j, quotEdge P j ≤ N) :
    uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
        ∏ i : Fin r, ((xi ((i : ℕ) + 1) (FreeGroup.lift σ w) : ℕ) : ℝ) ^ α i) =
      ∑ P ∈ (Finset.univ : Finset (Finpartition (Finset.univ :
          Finset (CycleVert (FreeGroup.reduceCyclically w.toWord) α)))).filter IsFoldFree,
        ((1 : ℝ) / N) ^ (((∑ j, quotEdge P j : ℕ) : ℤ) - quotVert P) *
          (∏ i ∈ Finset.Ico 1 (quotVert P), (1 - (i : ℝ) / N)) /
          ∏ j : Fin d, ∏ i ∈ Finset.Ico 1 (quotEdge P j), (1 - (i : ℝ) / N) := by
  sorry

end HananyPuder
