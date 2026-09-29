-- Prove2me | Theorems.Thm_MonoidHom_exists_subfield_units_coe_eq
-- name    : MonoidHom.exists_subfield_units_coe_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/21f3dc74-9f45-5e9d-9f04-02166ddc1a59
-- title:
--   Co-restricting a bimultiplicative pairing to a subfield
-- statement:
--   Let $G$ be a group, $L$ a field and $K \subseteq L$ a subfield. Let $F : G \to^* (G \to^* L^\times)$ be a monoid homomorphism from $G$ to the group of monoid homomorphisms from $G$ into the units of $L$; that is, $F$ is a bimultiplicative pairing $G \times G \to L^\times$. Assume that for all $\alpha, \beta \in G$ the image in $L$ of the unit $F\,\alpha\,\beta$ lies in $K$. The conclusion asserts the existence of a monoid homomorphism $F' : G \to^* (G \to^* K^\times)$ into the units of the subfield $K$ (viewed as a field in its own right) such that for all $\alpha, \beta \in G$ the image in $L$ of the element of $K$ underlying the unit $F'\,\alpha\,\beta$ equals the image in $L$ of $F\,\alpha\,\beta$. Thus a bimultiplicative pairing with values in $L^\times$ all of whose values lie in $K$ factors, compatibly with the inclusion $K \hookrightarrow L$, through $K^\times$; no claim of uniqueness of $F'$ is made.
--
--   This is the co-restriction (codomain restriction) of a bimultiplicative pairing along a subfield inclusion. It is used in the Čerednik–Drinfel'd part of the development, where a pairing constructed with values in the units of a larger field but known to take values in a smaller field of definition is read as a pairing into the units of that smaller field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MonoidHom_exists_subfield_units_coe_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem MonoidHom.exists_subfield_units_coe_eq
    {G : Type*} [Group G] {L : Type*} [Field L] (K : Subfield L)
    (F : G →* G →* Lˣ) (hF : ∀ α β : G, ((F α β : Lˣ) : L) ∈ K) :
    ∃ F' : G →* G →* (↥K)ˣ, ∀ α β : G, (((F' α β : (↥K)ˣ) : ↥K) : L) = F α β := by sorry
