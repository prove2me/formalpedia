-- Prove2me | Theorems.Thm_MooreFoelner_exists_const_mass_lt_of_isMarginal
-- name    : MooreFoelner.exists_const_mass_lt_of_isMarginal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-02T00:14:56.659426+00:00
-- url     : https://prove2.me/theorems/eb1abcef-c686-42f9-8484-327e20847b33
-- title:
--   Lemma 3.10 — marginal sets have relative weight O(ε) in every weighted ε-Følner set
-- statement:
--   Let $G$, with a finite symmetric generating set $\Gamma$, act partially on $S$. For every marginal $E \subseteq S$ there is a constant $C$ such that $\mu(E) < C\varepsilon\mu(S)$ for every $\varepsilon > 0$ and every weighted $\varepsilon$-Følner set $\mu$.
-- source:
--   Moore, J. T., Fast growth in the Følner function for Thompson's group F, Groups Geom. Dyn. 7 (2013) 633–651, https://doi.org/10.4171/GGD/201 (arXiv:0905.1118v7, whose page numbers are used), p. 8, Lemma 3.10

import Mathlib
import Definitions.Def_MooreFoelner

namespace MooreFoelner

theorem exists_const_mass_lt_of_isMarginal {G S : Type*} [Group G] (act : S → G → Option S)
    (hact : IsPartialAction act) (Γ : Finset G) (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ)
    (hgen : Subgroup.closure (Γ : Set G) = ⊤) (E : Set S) (hE : IsMarginal act E) :
    ∃ C : ℝ, ∀ (ε : ℝ), 0 < ε → ∀ μ : S →₀ ℝ, IsWeightedFolner act Γ μ ε →
      mass μ E < C * ε * mass μ Set.univ := by
  sorry

end MooreFoelner
