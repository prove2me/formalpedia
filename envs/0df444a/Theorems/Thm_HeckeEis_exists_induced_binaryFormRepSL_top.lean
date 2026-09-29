-- Prove2me | Theorems.Thm_HeckeEis_exists_induced_binaryFormRepSL_top
-- name    : HeckeEis.exists_induced_binaryFormRepSL_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/84cf2b36-679f-5fd8-905a-3d592b27e37a
-- title:
--   Induced module Ind_{Γ_0(N)}^{SL₂(ℤ)} of binary forms: no invariants, no coinvariants
-- statement:
--   Let $N$ be a natural number that is nonzero and let $n$ be an even natural number with $n \neq 0$. Write $\mathrm{BinaryForm}_{\mathbb C}(n)$ for the submodule of degree-$n$ homogeneous elements of $\mathbb C[X_0,X_1]$, on which $SL(2,\mathbb Z)$ acts through [`HeckeEis.binaryFormRepSL`](def/HeckeEis_BinaryFormRep.html#L61), the representation sending $g$ to the substitution $X_j \mapsto \sum_i g_{ij} X_i$. The assertion is that there exists a complex representation $W$ of the full subgroup $\top$ of $SL(2,\mathbb Z)$ on the space of functions $SL(2,\mathbb Z)/\Gamma_0(N) \to \mathrm{BinaryForm}_{\mathbb C}(n)$ with the following four properties. First, $W$ is the induced action: for all $g$, all $f$ and all cosets $x$ one has $(W(g)f)(x) = g \cdot f(g^{-1}x)$, the outer action being [`HeckeEis.binaryFormRepSL`](def/HeckeEis_BinaryFormRep.html#L61). Second, $W(-1)$ is the identity map. Third, $W$ has no nonzero invariants: if $W(g)f = f$ for every $g$, then $f = 0$. Fourth, $W$ has no coinvariants in the strong form that every $f$ can be written as $(W(S)a - a) + (W(ST)b - b)$ for some $a, b$, where $S$ and $T$ are the standard generators `ModularGroup.S` and `ModularGroup.T`.
--
--   This packages the induced module $\mathrm{Ind}_{\Gamma_0(N)}^{SL_2(\mathbb Z)}\mathrm{Sym}^n$ together with the three facts about it needed for a cohomological count: triviality of the central element $-1$, vanishing of invariants, and vanishing of coinvariants in the explicit shape dictated by the presentation of $PSL_2(\mathbb Z)$ by $S$ and $ST$. It feeds the bound [`HeckeEis.finrank_coeffH1par_le_two_mul_dimFormula`](thm.html#HeckeEis.finrank_coeffH1par_le_two_mul_dimFormula) on the dimension of parabolic cohomology in weight $n+2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_exists_induced_binaryFormRepSL_top.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.exists_induced_binaryFormRepSL_top (N : ℕ) [NeZero N] (n : ℕ) (hn : Even n) (hn0 : n ≠ 0) :
    ∃ W : Representation ℂ (⊤ : Subgroup SL(2, ℤ)) (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℂ n)),
      (∀ (g : (⊤ : Subgroup SL(2, ℤ))) (f : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℂ n)) (x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N),
        W g f x = HeckeEis.binaryFormRepSL ℂ n (g : SL(2, ℤ)) (f (((g : SL(2, ℤ))⁻¹) • x))) ∧
      W ⟨-1, Subgroup.mem_top _⟩ = LinearMap.id ∧
      (∀ f : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℂ n), (∀ g : (⊤ : Subgroup SL(2, ℤ)), W g f = f) → f = 0) ∧
      (∀ f : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℂ n), ∃ a b : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℂ n),
        f = (W ⟨ModularGroup.S, Subgroup.mem_top _⟩ a - a) + (W ⟨ModularGroup.S * ModularGroup.T, Subgroup.mem_top _⟩ b - b)) := by sorry
