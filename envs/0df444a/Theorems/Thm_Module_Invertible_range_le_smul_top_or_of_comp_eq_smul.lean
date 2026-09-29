-- Prove2me | Theorems.Thm_Module_Invertible_range_le_smul_top_or_of_comp_eq_smul
-- name    : Module.Invertible.range_le_smul_top_or_of_comp_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/2a05426c-5d07-5ec7-844a-717ce2a4b9ab
-- title:
--   Composite equal to a scalar in 𝔭: one image lies in 𝔭
-- statement:
--   Let $R$ be a commutative ring and let $P$ and $Q$ be $R$-modules (additive commutative groups with $R$-module structures) which are invertible in the sense of Mathlib's `Module.Invertible` class. Let $f : P \to Q$ and $g : Q \to P$ be $R$-linear maps and let $a \in R$ be such that the one-sided composite satisfies $g \circ f = a \cdot \mathrm{id}_P$ (no hypothesis is made on $f \circ g$). Let $x$ be a point of $\operatorname{Spec} R$, with associated prime ideal $\mathfrak p =$ `x.asIdeal`, and suppose $a \in \mathfrak p$. The conclusion is the disjunction: either the image submodule $\operatorname{range} f$ is contained in $\mathfrak p \cdot Q$ (the submodule $\mathfrak p \cdot \top$ of $Q$), or $\operatorname{range} g$ is contained in $\mathfrak p \cdot P$. Equivalently, at least one of $f$, $g$ becomes the zero map on the fibre at $\mathfrak p$.
--
--   For invertible (rank-one projective) modules the fibre at a prime is a line, so a factorisation of the scalar $a$ through two maps forces one of them to vanish modulo $\mathfrak p$ as soon as $a \in \mathfrak p$; this is the commutative-algebra input behind the statement that the two strata of a chart-local Drinfeld quadruple cover the base, where the composite of the two maps is the uniformiser. It is used in the Čerednik–Drinfeld part of the development, in the lemmas comparing Deligne and Drinfeld data on the formal model of the $p$-adic upper half plane.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_Invertible_range_le_smul_top_or_of_comp_eq_smul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Module.Invertible.range_le_smul_top_or_of_comp_eq_smul
    {R : Type*} [CommRing R] {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    [Module.Invertible R P] [Module.Invertible R Q] (f : P →ₗ[R] Q) (g : Q →ₗ[R] P) (a : R)
    (hfg : g ∘ₗ f = a • LinearMap.id) (x : PrimeSpectrum R) (ha : a ∈ x.asIdeal) :
    LinearMap.range f ≤ x.asIdeal • (⊤ : Submodule R Q) ∨ LinearMap.range g ≤ x.asIdeal • (⊤ : Submodule R P) := by sorry
