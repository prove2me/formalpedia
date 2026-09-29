-- Prove2me | Theorems.Thm_LanglandsTunnell_ArchPlace_forall_continuous_exists_eq_realCharFun_and_forall_continuous_exists_eq_complexCharFun
-- name    : LanglandsTunnell.ArchPlace.forall_continuous_exists_eq_realCharFun_and_forall_continuous_exists_eq_complexCharFun
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/76bb1e1f-5c7c-52ad-be89-4b4be0e717bd
-- title:
--   Continuous quasi-characters of ℝ^× and ℂ^×
-- statement:
--   The assertion is a conjunction of two classification statements. First: for every monoid homomorphism $\chi \colon \mathbb{R}^\times \to \mathbb{C}^\times$ between the unit groups of $\mathbb{R}$ and $\mathbb{C}$ which is continuous for their usual topologies, there exist a complex number $u$ and an element $a \in \mathbb{Z}/2$ with $\chi =$ `realCharFun` $u\,a$, that is, $\chi$ is the homomorphism sending a unit $x$ to $(|x| : \mathbb{C})^{u} \cdot (x/|x|)^{a.\mathrm{val}}$, where the first factor is the complex power of the real absolute value of $x$ viewed in $\mathbb{C}$, the second factor is the sign of $x$ regarded as a complex unit, and $a.\mathrm{val} \in \{0,1\}$ is the natural-number representative of $a$. Second: for every continuous monoid homomorphism $\chi \colon \mathbb{C}^\times \to \mathbb{C}^\times$ there exist a complex number $u$ and an integer $k$ with $\chi =$ `complexCharFun` $u\,k$, the homomorphism sending a unit $z$ to $(\|z\| : \mathbb{C})^{2u} \cdot (z/\|z\|)^{k}$, the second factor being an integer power of the angular part `anglePhase` $z = z/\|z\|$. Equality is equality of the bundled homomorphisms; no uniqueness of $u$, $a$ or $k$ is claimed, and no condition on $|\chi|$ is imposed, so these are quasi-characters rather than unitary characters.
--
--   This is the classification of continuous quasi-characters of the two archimedean local fields, in the explicit parametrisation by $(u,a)$ for $\mathbb{R}$ and $(u,k)$ for $\mathbb{C}$ used throughout the local archimedean theory. It is invoked in the analysis of intertwining operators and their normalisation by completed $L$-factors for induced representations at archimedean places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_ArchPlace_forall_continuous_exists_eq_realCharFun_and_forall_continuous_exists_eq_complexCharFun.lean

import Definitions.Def_LanglandsTunnell_ArchPlace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem
LanglandsTunnell.ArchPlace.forall_continuous_exists_eq_realCharFun_and_forall_continuous_exists_eq_complexCharFun :
    (∀ χ : ℝˣ →* ℂˣ, Continuous χ → ∃ (u : ℂ) (a : ZMod 2), χ = realCharFun u a) ∧
      (∀ χ : ℂˣ →* ℂˣ, Continuous χ → ∃ (u : ℂ) (k : ℤ), χ = complexCharFun u k) := by sorry
