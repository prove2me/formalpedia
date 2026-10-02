-- Prove2me | Theorems.Thm_MooreLiteralConnected_exists_rightMul_chain
-- name    : MooreLiteralConnected.exists_rightMul_chain
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-01T22:59:50.824419+00:00
-- url     : https://prove2.me/theorems/1d02b3af-bd3a-4205-93ae-34d9b36e472b
-- title:
--   Moore Definition 3.13 read literally: every subset of a group acting on itself is Γ-connected
-- statement:
--   Let $G$ be a group with a finite symmetric generating set $\Gamma$, acting on itself by right multiplication (`MooreFoelner.rightMul`). Then every $A \subseteq G$ satisfies the condition of Moore's Definition 3.13 as printed: for all $x, y \in A$ there are $\gamma_0, \dots, \gamma_{l-1} \in \Gamma$ such that, setting $x_0 = x$ and $x_{i+1} = x_i \gamma_i$, each $x_i$ is defined and $x_l = y$.
--
--   Moore's Definition 3.13 (p. 9) reads "A subset $A \subseteq G$ is $\Gamma$-connected if whenever $x$ and $y$ are in $A$, there are $\gamma_i$ ($i < l$) in $\Gamma$ such that, setting $x_0 = x$ and $x_{i+1} = x_i \cdot \gamma_i$, then $x_i$ is defined for each $i \le l$ and $y = x_l$." Read literally, as here, it holds for every subset, so the connectedness in Lemma 3.15 would say nothing, and the last step of the proof of Theorem 1.1 would fail: "Since $A'$ is $\Gamma$-connected, it must contain at least $\exp_n(0)$ elements" (p. 19) counts the points of a chain inside $A'$ from the identity to an element at distance at least $\exp_n(0)$. The Moore mission's definitions (`MooreFoelner.IsConnected`) require the chain to stay in $A$; the statement here is that condition with the requirement dropped.
-- source:
--   Moore, J. T., Fast growth in the Følner function for Thompson's group F, Groups Geom. Dyn. 7 (2013) 633–651, https://doi.org/10.4171/GGD/201 (arXiv:0905.1118v7 page numbers), p. 9, Definition 3.13 read literally, and p. 19, the last step of the proof of Theorem 1.1

import Definitions.Def_MooreFoelner
import Mathlib

namespace MooreLiteralConnected

theorem exists_rightMul_chain {G : Type*} [Group G] (Γ : Finset G) (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ)
    (hgen : Subgroup.closure (Γ : Set G) = ⊤) (A : Set G) :
    ∀ x ∈ A, ∀ y ∈ A, ∃ (l : ℕ) (p : Fin (l + 1) → G), p 0 = x ∧ p (Fin.last l) = y ∧
      ∀ i : Fin l, ∃ γ ∈ Γ, MooreFoelner.rightMul (p i.castSucc) γ = some (p i.succ) := by
  sorry

end MooreLiteralConnected
