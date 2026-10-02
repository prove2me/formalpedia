-- Prove2me | Theorems.Thm_MooreFoelner_finsum_abs_valAt_sub_lt
-- name    : MooreFoelner.finsum_abs_valAt_sub_lt
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-02T00:02:19.638352+00:00
-- url     : https://prove2.me/theorems/075d4734-b6c6-4ae0-a87e-9303e9a4ce12
-- title:
--   Lemma 3.5 — a weighted Følner set moves little under each nontrivial group element
-- statement:
--   Let $G$, with a finite symmetric generating set $\Gamma$, act partially on $S$, let $\varepsilon > 0$ and let $\mu$ be a weighted $\varepsilon$-Følner set. For every $g \ne e$, $\sum_{s \in S} |\mu(s \cdot g) - \mu(s)| < 2\varepsilon d_g \mu(S)$.
--
--   **Formalization Note.** Moore states this for every $g$; for $g = e$ both sides are $0$ and the strict inequality fails, so $g \ne e$ is assumed.
-- source:
--   Moore, J. T., Fast growth in the Følner function for Thompson's group F, Groups Geom. Dyn. 7 (2013) 633–651, https://doi.org/10.4171/GGD/201 (arXiv:0905.1118v7, whose page numbers are used), p. 6, Lemma 3.5

import Mathlib
import Definitions.Def_MooreFoelner

namespace MooreFoelner

theorem finsum_abs_valAt_sub_lt {G S : Type*} [Group G] (act : S → G → Option S)
    (hact : IsPartialAction act) (Γ : Finset G) (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ)
    (hgen : Subgroup.closure (Γ : Set G) = ⊤) (ε : ℝ) (hε : 0 < ε) (μ : S →₀ ℝ)
    (hμ : IsWeightedFolner act Γ μ ε) (g : G) (hg : g ≠ 1) :
    ∑ᶠ s, |valAt act μ s g - μ s| < 2 * ε * wordLength Γ g * mass μ Set.univ := by
  sorry

end MooreFoelner
