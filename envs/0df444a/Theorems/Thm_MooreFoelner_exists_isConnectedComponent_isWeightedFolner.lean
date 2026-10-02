-- Prove2me | Theorems.Thm_MooreFoelner_exists_isConnectedComponent_isWeightedFolner
-- name    : MooreFoelner.exists_isConnectedComponent_isWeightedFolner
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-02T00:27:55.533049+00:00
-- url     : https://prove2.me/theorems/de7e97b5-dc7e-4932-8fee-550ac2b8cf03
-- title:
--   Lemma 3.14 — some connected component of the support carries a Følner piece
-- statement:
--   Let $G$, with a finite symmetric generating set $\Gamma$, act partially on $S$, let $\varepsilon > 0$ and let $\mu$ be a weighted $\varepsilon$-Følner set. Some $\Gamma$-connected component $A$ of the support of $\mu$ has $\mu \restriction A$ a weighted $\varepsilon$-Følner set.
-- source:
--   Moore, J. T., Fast growth in the Følner function for Thompson's group F, Groups Geom. Dyn. 7 (2013) 633–651, https://doi.org/10.4171/GGD/201 (arXiv:0905.1118v7, whose page numbers are used), p. 9, Lemma 3.14

import Mathlib
import Definitions.Def_MooreFoelner

namespace MooreFoelner

theorem exists_isConnectedComponent_isWeightedFolner {G S : Type*} [Group G]
    (act : S → G → Option S) (hact : IsPartialAction act) (Γ : Finset G)
    (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) (hgen : Subgroup.closure (Γ : Set G) = ⊤) (ε : ℝ) (hε : 0 < ε)
    (μ : S →₀ ℝ) (hμ : IsWeightedFolner act Γ μ ε) :
    ∃ A : Set S, IsConnectedComponent act Γ A ↑μ.support ∧
      IsWeightedFolner act Γ (restrict μ A) ε := by
  sorry

end MooreFoelner
