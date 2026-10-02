-- Prove2me | Theorems.Thm_MooreFoelner_exists_isConnected_isFolnerSet_one_mem
-- name    : MooreFoelner.exists_isConnected_isFolnerSet_one_mem
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-02T00:34:03.532565+00:00
-- url     : https://prove2.me/theorems/af690316-bdfb-404b-bdd6-450fb5b7ea17
-- title:
--   Lemma 3.15 — a Følner set can be replaced by a connected one containing the identity
-- statement:
--   Let $G$ have a finite symmetric generating set $\Gamma$. If $A \subseteq G$ is $\varepsilon$-Følner (right translates), there is an $\varepsilon$-Følner $B \subseteq G$ that is $\Gamma$-connected for the right action of $G$ on itself, contains the identity, and has $|B| \le |A|$.
--
--   **Formalization Note.** Moore states this for a finite generating set; the section's standing assumption that $\Gamma$ is symmetric is included.
-- source:
--   Moore, J. T., Fast growth in the Følner function for Thompson's group F, Groups Geom. Dyn. 7 (2013) 633–651, https://doi.org/10.4171/GGD/201 (arXiv:0905.1118v7, whose page numbers are used), p. 9, Lemma 3.15

import Mathlib
import Definitions.Def_MooreFoelner

namespace MooreFoelner

theorem exists_isConnected_isFolnerSet_one_mem {G : Type*} [Group G] (Γ : Finset G)
    (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) (hgen : Subgroup.closure (Γ : Set G) = ⊤) (ε : ℝ)
    (A : Finset G) (hA : IsFolnerSet Γ A ε) :
    ∃ B : Finset G, IsFolnerSet Γ B ε ∧ IsConnected rightMul Γ ↑B ∧ (1 : G) ∈ B ∧
      B.card ≤ A.card := by
  sorry

end MooreFoelner
