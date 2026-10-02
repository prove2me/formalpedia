-- Prove2me | Theorems.Thm_MooreFoelner_not_eventually_folnerFunction_le_towerExp
-- name    : MooreFoelner.not_eventually_folnerFunction_le_towerExp
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-01T23:04:57.532474+00:00
-- url     : https://prove2.me/theorems/38904793-555d-4601-84ff-482aaf6ee945
-- title:
--   Theorem 1.1, second sentence — the Følner function of F is not eventually dominated by any tower
-- statement:
--   For every finite symmetric generating set $\Gamma$ of Moore's $F$ and every $p$, it is not the case that $\mathrm{Føl}_{F,\Gamma}(n) \le \exp_p(n)$ for all sufficiently large $n$.
-- source:
--   Moore, J. T., Fast growth in the Følner function for Thompson's group F, Groups Geom. Dyn. 7 (2013) 633–651, https://doi.org/10.4171/GGD/201 (arXiv:0905.1118v7, whose page numbers are used), p. 2, Theorem 1.1, second sentence

import Mathlib
import Definitions.Def_MooreFoelner
import Definitions.Def_MooreTrees
import Definitions.Def_ThompsonAmenability

namespace MooreFoelner

theorem not_eventually_folnerFunction_le_towerExp (Γ : Finset MooreF)
    (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) (hgen : Subgroup.closure (Γ : Set MooreF) = ⊤) (p : ℕ) :
    ¬ ∃ N : ℕ, ∀ n ≥ N, folnerFunction Γ n ≤ (ThompsonAmenability.towerExp p n : ℕ∞) := by
  sorry

end MooreFoelner
