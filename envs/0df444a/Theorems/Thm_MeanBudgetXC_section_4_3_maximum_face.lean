-- Prove2me | Theorems.Thm_MeanBudgetXC_section_4_3_maximum_face
-- name    : MeanBudgetXC.section_4_3_maximum_face
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:43:24.190769+00:00
-- url     : https://prove2.me/theorems/b23c8f18-23c5-45b9-9388-8e243ba8ccd8
-- title:
--   Section 4.3, Eq. (16) — the maximum face of $C_Q$ is the hull of the canonical coverage points
-- statement:
--   Let $Q$ be the host graph, $m=n_0^2$, $d=4n_0+v\ell+c$, and give each heavy edge weight $L_{\mathrm{heavy}}>4m$ and each interaction edge weight one. With $\Phi_{\max}=L_{\mathrm{heavy}}m_{\mathrm{heavy}}+3m$:
--
--   1. $\alpha_{\mathrm{anc}}\cdot y\le\Phi_{\max}$ on $C_Q$;
--   2. every canonical choice has anchor value $\Phi_{\max}$;
--   3. $\alpha_{\mathrm{anc}}\cdot\mathbf 1_E=L_{\mathrm{heavy}}m_{\mathrm{heavy}}+4m$;
--   4. the entire maximum face of $C_Q$ is the convex hull of exactly the canonical coverage points.
--
--   The maximum face encodes independent source bits, which is the source of the exponential lower bound.
--
--   Differences from the source:
--   - generalization: the host at the parameters (15), with a triangle-free $T$ and $\rho>\max\{\theta,1/2\}$ → the host at arbitrary parameters and any graph $T$, with $d=4n_0+v\ell+c$; reason: the face computation uses only $d=4n_0+v\ell+c$ and $L_{\mathrm{heavy}}>4m$; the paper's host is a special case
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Section 4.3, display (16), p.19

import Mathlib
import Definitions.Def_MeanBudgetXC_budgetCoeffBody
import Definitions.Def_ZeroOneExpansion_exposedFace
import Definitions.Def_MeanBudgetXC_anchorWeight
import Definitions.Def_MeanBudgetXC_heavyCount
import Definitions.Def_MeanBudgetXC_IsCanonical

namespace MeanBudgetXC

open Matrix

/-- **Section 4.3, the maximum face of `C_Q`**, with display (16) (Chao–Gao–Qi–Wang, *A Sharp
Mean-Budget Transition for Local Pair Marginals*, STOC 2027 submission, manuscript sha256
882d9c71…9e76, Section 4.3, p.19). Let `Q` be the host graph, `d = 4n₀ + vℓ + c`, and give each
heavy edge weight `L_heavy > 4m` (`m = n₀²`) and each interaction edge weight one. With
`Φ_max = L_heavy m_heavy + 3m`:
1. `α_anc · y ≤ Φ_max` on `C_Q`;
2. every canonical choice has anchor value `Φ_max`;
3. `α_anc · 1_E = L_heavy m_heavy + 4m` (16);
4. the entire maximum face of `C_Q` is the convex hull of exactly the canonical coverage points.

**Formalization Note** The maximum face is the published `ZeroOneExpansion.exposedFace` (the set of
maximizers of a linear functional on the body). The canonical choices are those of `IsCanonical`; `v` is Mathlib's
`vertexCoverNum` of `T`. No hypothesis on `T` (triangle-freeness, the ratio `ρ`) is needed for
this face computation, so none is assumed. -/
theorem section_4_3_maximum_face (n₀ t ℓ c niso d : ℕ) (T : SimpleGraph (Fin t))
    [DecidableRel T.Adj] (hd : d = 4 * n₀ + T.vertexCoverNum.toNat * ℓ + c) (L : ℝ)
    (hL : 4 * (n₀ : ℝ) ^ 2 < L) :
    (∀ y ∈ coeffBody (hostGraph n₀ t ℓ c niso T) d,
        anchorWeight n₀ t ℓ c niso T L ⬝ᵥ y ≤ L * heavyCount n₀ ℓ c T + 3 * (n₀ : ℝ) ^ 2) ∧
      (∀ S : Finset (HostV n₀ t ℓ c niso), IsCanonical T S →
        anchorWeight n₀ t ℓ c niso T L ⬝ᵥ coverVec (hostGraph n₀ t ℓ c niso T) S =
          L * heavyCount n₀ ℓ c T + 3 * (n₀ : ℝ) ^ 2) ∧
      (anchorWeight n₀ t ℓ c niso T L ⬝ᵥ fun _ => 1) = L * heavyCount n₀ ℓ c T + 4 * (n₀ : ℝ) ^ 2 ∧
      ZeroOneExpansion.exposedFace (coeffBody (hostGraph n₀ t ℓ c niso T) d)
          (fun y => anchorWeight n₀ t ℓ c niso T L ⬝ᵥ y) =
        convexHull ℝ {y | ∃ S : Finset (HostV n₀ t ℓ c niso), IsCanonical T S ∧
          y = coverVec (hostGraph n₀ t ℓ c niso T) S} := by sorry

end MeanBudgetXC
