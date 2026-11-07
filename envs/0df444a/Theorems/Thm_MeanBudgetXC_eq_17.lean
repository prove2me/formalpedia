-- Prove2me | Theorems.Thm_MeanBudgetXC_eq_17
-- name    : MeanBudgetXC.eq_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:43:18.822435+00:00
-- url     : https://prove2.me/theorems/bf911c6b-d963-4356-b60b-10f1767e5b4c
-- title:
--   Eq. (17) with (18), first inequality — $\mathrm{xc}(C_Q)$ and $\mathrm{xc}(C_{Q,B})$ dominate $\mathrm{xc}(\mathrm{COR}(n_0))$
-- statement:
--   Let $Q$ be the host graph with $n_0\ge1$, $m=n_0^2$ and $d=4n_0+v\ell+c$.
--
--   1. $\mathrm{xc}(C_Q)\ge\mathrm{xc}(\mathrm{COR}(n_0))$, the first inequality of (17).
--   2. For a mean budget $B>2$, the heavy weight
--   $$L_{\mathrm{heavy}}=4m+1+\frac{8m}{(B-2)m_{\mathrm{heavy}}}\tag{18}$$
--   has $L_{\mathrm{heavy}}>4m$ and
--   $$B\Phi_{\max}-2\alpha_{\mathrm{anc}}\cdot\mathbf 1_E=(B-2)L_{\mathrm{heavy}}m_{\mathrm{heavy}}+(3B-8)m=(B-2)(4m+1)m_{\mathrm{heavy}}+3Bm>0.$$
--   The whole anchor maximum face of $C_{Q,B}$ is the same as that of $C_Q$, and $\mathrm{xc}(C_{Q,B})\ge\mathrm{xc}(\mathrm{COR}(n_0))$.
--
--   The second inequality of (17), $\mathrm{xc}(\mathrm{COR}(n_0))\ge2^{c_*n_0}$, is the correlation-polytope lower bound of Fiorini et al., already proved on the platform as `ExtensionComplexity.TSP.xc_cor_lower_bound`, and is a reference item of this mission.
--
--   Differences from the source:
--   - generalization: the host at the parameters (15), with a triangle-free $T$ → the host at arbitrary parameters and any graph $T$, with $n_0\ge1$ and $d=4n_0+v\ell+c$; reason: the argument uses only these; the paper's host is a special case
--   - encoding: $\mathrm{COR}(n_0)$ in the coordinates $(z_i)_i$ and $(z_iz_j)_{i<j}$ → the platform's `corPolytope` in $n_0\times n_0$ matrix coordinates; reason: the two are linearly isomorphic, since the matrix is symmetric with diagonal $z_i$, so they have the same extension complexity
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Section 4.4, displays (17) and (18), p.20

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_ExtensionComplexity_TSP_CutCor
import Definitions.Def_MeanBudgetXC_budgetCoeffBody
import Definitions.Def_ZeroOneExpansion_exposedFace
import Definitions.Def_MeanBudgetXC_anchorWeight
import Definitions.Def_MeanBudgetXC_heavyCount

namespace MeanBudgetXC

open Matrix ExtensionComplexity.TSP

/-- **Display (17), with (18)** (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair
Marginals*, STOC 2027 submission, manuscript sha256 882d9c71…9e76, Section 4.4, p.20). For the
host `Q` with `n₀ ≥ 1` and `d = 4n₀ + vℓ + c`:
1. `xc(C_Q) ≥ xc(COR(n₀))` (the first inequality of (17));
2. for a finite mean budget `B > 2`, the heavy weight
   `L_heavy = 4m + 1 + 8m/((B − 2) m_heavy)` of (18) has `L_heavy > 4m` and
   `BΦ_max − 2 α_anc · 1_E = (B − 2) L_heavy m_heavy + (3B − 8)m = (B − 2)(4m + 1) m_heavy + 3Bm > 0`;
   the whole anchor maximum face of `C_{Q,B}` is the same as that of `C_Q`, and (17) holds for
   `C_{Q,B}`: `xc(C_{Q,B}) ≥ xc(COR(n₀))`.

**Formalization Note** The maximum face is the published `ZeroOneExpansion.exposedFace`. `COR(n₀)` is the platform's `corPolytope n₀ = conv{b bᵀ : b ∈ {0,1}^{n₀}}`
in `n₀ × n₀` matrix coordinates; the paper's `COR(n₀)` uses the coordinates `(z_i)_i` and
`(z_i z_j)_{i<j}`. The two are linearly isomorphic (the matrix is symmetric with diagonal `z_i`),
so they have the same extension complexity. `m = n₀²`; `Φ_max = L_heavy m_heavy + 3m`. -/
theorem eq_17 (n₀ t ℓ c niso d : ℕ) (T : SimpleGraph (Fin t)) [DecidableRel T.Adj]
    (hn₀ : 1 ≤ n₀) (hd : d = 4 * n₀ + T.vertexCoverNum.toNat * ℓ + c) :
    extensionComplexity (corPolytope n₀) ≤
        extensionComplexity (coeffBody (hostGraph n₀ t ℓ c niso T) d) ∧
      ∀ B : ℝ, 2 < B →
        let m : ℝ := (n₀ : ℝ) ^ 2
        let mh : ℝ := heavyCount n₀ ℓ c T
        let L : ℝ := 4 * m + 1 + 8 * m / ((B - 2) * mh)
        4 * m < L ∧
          B * (L * mh + 3 * m) - 2 * (anchorWeight n₀ t ℓ c niso T L ⬝ᵥ fun _ => 1) =
            (B - 2) * L * mh + (3 * B - 8) * m ∧
          (B - 2) * L * mh + (3 * B - 8) * m = (B - 2) * (4 * m + 1) * mh + 3 * B * m ∧
          0 < (B - 2) * (4 * m + 1) * mh + 3 * B * m ∧
          ZeroOneExpansion.exposedFace (budgetCoeffBody (hostGraph n₀ t ℓ c niso T) d B)
          (fun y => anchorWeight n₀ t ℓ c niso T L ⬝ᵥ y) =
            ZeroOneExpansion.exposedFace (coeffBody (hostGraph n₀ t ℓ c niso T) d)
          (fun y => anchorWeight n₀ t ℓ c niso T L ⬝ᵥ y) ∧
          extensionComplexity (corPolytope n₀) ≤
            extensionComplexity (budgetCoeffBody (hostGraph n₀ t ℓ c niso T) d B) := by sorry

end MeanBudgetXC
