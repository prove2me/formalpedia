-- Prove2me | Theorems.Thm_MooreFoelner_mass_lt_of_marginalizes
-- name    : MooreFoelner.mass_lt_of_marginalizes
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-02T00:08:33.281486+00:00
-- url     : https://prove2.me/theorems/6d99ec94-6ff3-4f5d-946b-c3bf6c87cbae
-- title:
--   Lemma 3.9 — a set marginalized off the complement of the support has small weight
-- statement:
--   Let $G$, with a finite symmetric generating set $\Gamma$, act partially on $S$, let $\varepsilon > 0$ and let $\mu$ be a weighted $\varepsilon$-Følner set with support $A$. If $g \ne e$ marginalizes $E \subseteq S$ off $S \setminus A$, then $\mu(E) < d_g \varepsilon \mu(S)$.
--
--   **Formalization Note.** For $g = e$ the hypothesis forces $\mu(E) = 0$ and the strict inequality fails, so $g \ne e$ is assumed. Moore's proof bounds $\mu(E)$ by $\sum_s |\mu(s \cdot g) - \mu(s)|$ over disjoint chains and applies Lemma 3.5 once, which gives $2 d_g$ in place of $d_g$; the statement keeps Moore's $d_g$, which follows by counting only the decreases $\mu(u) - \mu(u \cdot \gamma)$ along a shortest word for $g$ (each step is bounded by one term of the Følner sum) and using $d_g \ge 1$.
-- source:
--   Moore, J. T., Fast growth in the Følner function for Thompson's group F, Groups Geom. Dyn. 7 (2013) 633–651, https://doi.org/10.4171/GGD/201 (arXiv:0905.1118v7, whose page numbers are used), p. 7, Lemma 3.9

import Mathlib
import Definitions.Def_MooreFoelner

namespace MooreFoelner

theorem mass_lt_of_marginalizes {G S : Type*} [Group G] (act : S → G → Option S)
    (hact : IsPartialAction act) (Γ : Finset G) (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ)
    (hgen : Subgroup.closure (Γ : Set G) = ⊤) (ε : ℝ) (hε : 0 < ε) (μ : S →₀ ℝ)
    (hμ : IsWeightedFolner act Γ μ ε) (E : Set S) (g : G) (hg : g ≠ 1)
    (hE : Marginalizes act g E (↑μ.support)ᶜ) :
    mass μ E < wordLength Γ g * ε * mass μ Set.univ := by
  sorry

end MooreFoelner
