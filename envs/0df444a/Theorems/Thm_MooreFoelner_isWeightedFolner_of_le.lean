-- Prove2me | Theorems.Thm_MooreFoelner_isWeightedFolner_of_le
-- name    : MooreFoelner.isWeightedFolner_of_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-02T00:20:52.453605+00:00
-- url     : https://prove2.me/theorems/809f132e-dab3-4819-b874-b7e85ee90721
-- title:
--   Lemma 3.11 — a large piece of a weighted Følner set is weighted Følner
-- statement:
--   Let $G$, with a finite symmetric generating set $\Gamma$, act partially on $S$, and let $\mu$ be a weighted $\varepsilon$-Følner set. If $\nu$ is finitely supported with values in $[0,\infty)$, $\nu \le \mu$ pointwise, and $\nu(S) \ge (1 - \delta)\mu(S)$ for some $0 < \delta < 1$, then $\nu$ is a weighted $(\varepsilon + 2|\Gamma|\delta)/(1 - \delta)$-Følner set.
-- source:
--   Moore, J. T., Fast growth in the Følner function for Thompson's group F, Groups Geom. Dyn. 7 (2013) 633–651, https://doi.org/10.4171/GGD/201 (arXiv:0905.1118v7, whose page numbers are used), p. 8, Lemma 3.11

import Mathlib
import Definitions.Def_MooreFoelner

namespace MooreFoelner

theorem isWeightedFolner_of_le {G S : Type*} [Group G] (act : S → G → Option S)
    (hact : IsPartialAction act) (Γ : Finset G) (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ)
    (hgen : Subgroup.closure (Γ : Set G) = ⊤) (ε δ : ℝ) (μ ν : S →₀ ℝ)
    (hμ : IsWeightedFolner act Γ μ ε) (hν : ∀ s, 0 ≤ ν s) (hle : ∀ s, ν s ≤ μ s)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hmass : mass ν Set.univ ≥ (1 - δ) * mass μ Set.univ) :
    IsWeightedFolner act Γ ν ((ε + 2 * Γ.card * δ) / (1 - δ)) := by
  sorry

end MooreFoelner
