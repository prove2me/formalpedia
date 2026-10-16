-- Prove2me | Theorems.Thm_MazurTransfer_exists_character_inclusion_for_selected_one_dimensional_quotient
-- name    : MazurTransfer.exists_character_inclusion_for_selected_one_dimensional_quotient
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-16T06:00:04.089317+00:00
-- url     : https://prove2.me/theorems/304a7ac7-8c8f-4aa2-bc7d-af585bb838d3
-- title:
--   A fixed one-dimensional quotient retains an exact character kernel
-- statement:
--   Let $k$ be a field and $G$ a group. Let $\sigma$, $\rho$, and $\tau$ be $k$-linear representations of $G$, with $\sigma$ on $k$, $\rho$ on a finite-dimensional space $V$, and $\tau$ on a one-dimensional space $B$. Suppose intertwining maps $i:\sigma\to\rho$ and $q:\rho\to\tau$ form a short exact sequence. Then for every given surjective intertwining map $p:\rho\to\tau$, there is an injective intertwining map $j:\sigma\to\rho$ whose image is exactly $\ker p$. No splitting or distinctness of the characters is required.
-- source:
--   Derived representation-theoretic lemma for MazurTorsion order-13 descent. Primary APIs: Mathlib at 0df444a360eaa60ab8c11dca51a86af692955474, RepresentationTheory/Intertwining.lean (https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RepresentationTheory/Intertwining.lean), and finite-dimensional linear algebra. Proof by separating whether the given quotient annihilates the original character line; otherwise its restriction to that line is an isomorphism.

import Mathlib

theorem MazurTransfer.exists_character_inclusion_for_selected_one_dimensional_quotient :
    ∀ (k G V B : Type) [Field k] [Group G]
    [AddCommGroup V] [Module k V] [AddCommGroup B] [Module k B]
    [FiniteDimensional k V] [FiniteDimensional k B]
    (σ : Representation k G k) (ρ : Representation k G V) (τ : Representation k G B)
    (hB : Module.finrank k B = 1)
    (i : Representation.IntertwiningMap σ ρ) (q : Representation.IntertwiningMap ρ τ)
    (hi : Function.Injective i) (hq : Function.Surjective q)
    (hk : LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap)
    (p : Representation.IntertwiningMap ρ τ) (hp : Function.Surjective p),
    ∃ j : Representation.IntertwiningMap σ ρ,
      Function.Injective j ∧ LinearMap.range j.toLinearMap = LinearMap.ker p.toLinearMap := by sorry
