-- Prove2me | Theorems.Thm_HananyPuder_tendsto_uniformExp_trace_youngAct_of_isNonPower
-- name    : HananyPuder.tendsto_uniformExp_trace_youngAct_of_isNonPower
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T22:13:06.746948+00:00
-- url     : https://prove2.me/theorems/ea847045-ebaf-4bf1-93df-29e1af93c4b6
-- title:
--   Hanany–Puder, Corollary 1.7 — for a non-power w and a stable irreducible character χ ≠ 1, ξ₁ − 1, E_w[χ] → 0
-- statement:
--   Let $\lambda$ be a base partition (a `YoungDiagram`) other than the empty partition and the partition $(1)$, that is, with row lengths (`rowLens`) neither $[\,]$ nor $[1]$. Let $\chi_N$ be the character of the representation of $\mathbf S_N$ defined by $\lambda[N] = (N - |\lambda|, \lambda_1, \dots, \lambda_\ell)$: the trace of `youngAct N (stableRows λ N) σ` on `youngSpace N (stableRows λ N)`. Let $w \in \mathbf F_d$ be a non-power (`IsNonPower`). Then
--   $$\lim_{N\to\infty} \mathbf E_{w,N}[\operatorname{Re}\chi_N] = 0,$$
--   where $\mathbf E_{w,N}$ is the expectation over i.i.d. uniform $\sigma_1, \dots, \sigma_d \in \mathbf S_N$ of a function of $w(\sigma_1, \dots, \sigma_d)$ (`FreeGroup.lift σ w`).
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 31, the corollary of Hanany–Puder cited in the proof of Lemma 10.2, which cites Hanany, L. and Puder, D., Word measures on symmetric groups, Int. Math. Res. Not. IMRN 2023 (2023) 9221–9297, https://doi.org/10.1093/imrn/rnac084 (arXiv:2009.00897v4), Corollary 1.7

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_StrongConvG4

open Filter Topology StrongConv

namespace HananyPuder

theorem tendsto_uniformExp_trace_youngAct_of_isNonPower (μ : YoungDiagram) (hμ₀ : μ.rowLens ≠ [])
    (hμ₁ : μ.rowLens ≠ [1]) {d : ℕ} (w : FreeGroup (Fin d)) (hw : IsNonPower w) :
    Tendsto (fun N : ℕ => uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
        (LinearMap.trace ℂ (youngSpace N (stableRows μ N))
          (youngAct N (stableRows μ N) (FreeGroup.lift σ w))).re))
      atTop (𝓝 0) := by
  sorry

end HananyPuder
