-- Prove2me | Theorems.Thm_MooreFoelner_exists_const_forall_isFolnerSet_towerExp_le_card
-- name    : MooreFoelner.exists_const_forall_isFolnerSet_towerExp_le_card
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-01T23:00:14.197121+00:00
-- url     : https://prove2.me/theorems/b18374c9-3203-47ec-995b-19029d13fb76
-- title:
--   Theorem 1.1 — Følner sets of F have at least tower-many elements (Moore's conventions)
-- statement:
--   For every finite symmetric generating set $\Gamma$ of Moore's $F$ (the product "$f$ followed by $g$") there is a constant $C > 1$ such that, for every $n$, every finite $A \subseteq F$ that is $C^{-n}$-Følner with respect to $\Gamma$ (right translates, `IsFolnerSet`) has at least $\exp_n(0)$ elements, where $\exp_0(n) = n$ and $\exp_{p+1}(n) = 2^{\exp_p(n)}$.
-- source:
--   Moore, J. T., Fast growth in the Følner function for Thompson's group F, Groups Geom. Dyn. 7 (2013) 633–651, https://doi.org/10.4171/GGD/201 (arXiv:0905.1118v7, whose page numbers are used), p. 2, Theorem 1.1

import Mathlib
import Definitions.Def_MooreFoelner
import Definitions.Def_MooreTrees
import Definitions.Def_ThompsonAmenability

namespace MooreFoelner

theorem exists_const_forall_isFolnerSet_towerExp_le_card (Γ : Finset MooreF)
    (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) (hgen : Subgroup.closure (Γ : Set MooreF) = ⊤) :
    ∃ C : ℝ, 1 < C ∧ ∀ (n : ℕ) (A : Finset MooreF),
      IsFolnerSet Γ A (C ^ (-(n : ℤ))) → ThompsonAmenability.towerExp n 0 ≤ A.card := by
  sorry

end MooreFoelner
