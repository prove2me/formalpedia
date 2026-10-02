-- Prove2me | Theorems.Thm_MooreFoelner_isWeightedFolner_mapDomain
-- name    : MooreFoelner.isWeightedFolner_mapDomain
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-01T23:58:14.895602+00:00
-- url     : https://prove2.me/theorems/e4b5a665-19fd-4c03-a18a-e9e8a3ff72b2
-- title:
--   Lemma 3.4 — pushing a weighted Følner set forward along an equivariant map
-- statement:
--   Let $G$, with a finite symmetric generating set $\Gamma$, act partially on $S$ and on $T$, and let $\mu$ be a weighted $\varepsilon$-Følner set for the action on $S$. If $h \colon S \to T$ satisfies $h(s \cdot \gamma) = h(s) \cdot \gamma$, both sides defined, whenever $\gamma \in \Gamma$ and $\mu(s) + \mu(s \cdot \gamma) > 0$, then $\nu(t) = \sum_{h(s) = t} \mu(s)$ (`Finsupp.mapDomain h μ`) is a weighted $\varepsilon$-Følner set for the action on $T$.
-- source:
--   Moore, J. T., Fast growth in the Følner function for Thompson's group F, Groups Geom. Dyn. 7 (2013) 633–651, https://doi.org/10.4171/GGD/201 (arXiv:0905.1118v7, whose page numbers are used), p. 5, Lemma 3.4

import Mathlib
import Definitions.Def_MooreFoelner

namespace MooreFoelner

theorem isWeightedFolner_mapDomain {G S T : Type*} [Group G] (actS : S → G → Option S)
    (actT : T → G → Option T) (hS : IsPartialAction actS) (hT : IsPartialAction actT)
    (Γ : Finset G) (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) (hgen : Subgroup.closure (Γ : Set G) = ⊤)
    (μ : S →₀ ℝ) (ε : ℝ) (hμ : IsWeightedFolner actS Γ μ ε) (h : S → T)
    (hh : ∀ γ ∈ Γ, ∀ s, 0 < μ s + valAt actS μ s γ →
      ∃ y, actS s γ = some y ∧ actT (h s) γ = some (h y)) :
    IsWeightedFolner actT Γ (μ.mapDomain h) ε := by
  sorry

end MooreFoelner
