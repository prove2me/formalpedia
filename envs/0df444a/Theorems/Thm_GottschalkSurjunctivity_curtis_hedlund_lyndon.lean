-- Prove2me | Theorems.Thm_GottschalkSurjunctivity_curtis_hedlund_lyndon
-- name    : GottschalkSurjunctivity.curtis_hedlund_lyndon
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-30T14:09:51.637867+00:00
-- url     : https://prove2.me/theorems/c6a858d9-f856-4c42-b49b-aac905b32929
-- title:
--   Curtis–Hedlund–Lyndon theorem
-- statement:
--   **Curtis–Hedlund–Lyndon theorem.** Let $G$ be a group and $A$ a finite set with the discrete topology; give $A^G$ the product topology. A map $\tau : A^G \to A^G$ is continuous and commutes with the left shift,
--   $$\tau(g\cdot x) = g\cdot\tau(x), \qquad (g\cdot x)(h) = x(g^{-1}h),$$
--   if and only if it is a cellular automaton: there are a finite set $S \subseteq G$ and a map $\mu : A^S \to A$ with
--   $$\tau(x)(g) = \mu\big(s\mapsto x(gs)\big) \qquad \text{for all } x \in A^G,\ g \in G.$$
--
--   This identifies the maps in the definition of surjunctivity with cellular automata.
-- source:
--   G. A. Hedlund, Endomorphisms and automorphisms of the shift dynamical system, Math. Systems Theory 3 (1969) 320-375, https://doi.org/10.1007/BF01691062; general groups: T. Ceccherini-Silberstein, M. Coornaert, Cellular Automata and Groups, Springer 2010, https://doi.org/10.1007/978-3-642-14034-1, Section 1.8 (Curtis-Hedlund theorem)

import Mathlib
import Definitions.Def_GottschalkSurjunctivity_Defs

namespace GottschalkSurjunctivity

theorem curtis_hedlund_lyndon (G : Type) [Group G] (A : Type) [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] (τ : (G → A) → (G → A)) :
    (Continuous τ ∧ IsShiftEquivariant G τ) ↔ IsCellularAutomaton G τ := by sorry

end GottschalkSurjunctivity
