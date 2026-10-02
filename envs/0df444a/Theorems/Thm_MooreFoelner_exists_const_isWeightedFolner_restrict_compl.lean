-- Prove2me | Theorems.Thm_MooreFoelner_exists_const_isWeightedFolner_restrict_compl
-- name    : MooreFoelner.exists_const_isWeightedFolner_restrict_compl
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-02T00:24:54.147165+00:00
-- url     : https://prove2.me/theorems/cbde493d-418d-4150-8b4c-9e08a49b1929
-- title:
--   Lemma 3.12 — removing a marginal set keeps a weighted Følner set Følner
-- statement:
--   Let $G$, with a finite symmetric generating set $\Gamma$, act partially on $S$, and let $E \subseteq S$ be marginal with $S \setminus E$ non-empty. There is a constant $C$ such that whenever $\mu$ is a weighted $\varepsilon$-Følner set and $C\varepsilon \le 1$, $\mu \restriction (S \setminus E)$ is a weighted $C\varepsilon$-Følner set with non-empty support.
-- source:
--   Moore, J. T., Fast growth in the Følner function for Thompson's group F, Groups Geom. Dyn. 7 (2013) 633–651, https://doi.org/10.4171/GGD/201 (arXiv:0905.1118v7, whose page numbers are used), p. 9, Lemma 3.12

import Mathlib
import Definitions.Def_MooreFoelner

namespace MooreFoelner

theorem exists_const_isWeightedFolner_restrict_compl {G S : Type*} [Group G]
    (act : S → G → Option S) (hact : IsPartialAction act) (Γ : Finset G)
    (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) (hgen : Subgroup.closure (Γ : Set G) = ⊤) (E : Set S)
    (hE : IsMarginal act E) (hne : (Eᶜ).Nonempty) :
    ∃ C : ℝ, ∀ (ε : ℝ) (μ : S →₀ ℝ), IsWeightedFolner act Γ μ ε → C * ε ≤ 1 →
      IsWeightedFolner act Γ (restrict μ Eᶜ) (C * ε) ∧ (restrict μ Eᶜ).support.Nonempty := by
  sorry

end MooreFoelner
