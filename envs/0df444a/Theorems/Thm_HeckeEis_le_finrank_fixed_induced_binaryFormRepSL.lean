-- Prove2me | Theorems.Thm_HeckeEis_le_finrank_fixed_induced_binaryFormRepSL
-- name    : HeckeEis.le_finrank_fixed_induced_binaryFormRepSL
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/97044c7f-6184-5086-9b7d-a2178cc068c0
-- title:
--   Fixed vectors in Ind_{Γ_0(N)}^{SL₂(ℤ)} of binary forms
-- statement:
--   Let $N\ge 1$ (a natural number with `NeZero N`) and let $n$ be an even natural number. Write $X = SL(2,\mathbb Z)/\Gamma_0(N)$ for the coset space and $V_n =$ [`HeckeEis.BinaryForm ℂ n`](def/HeckeEis_BinaryFormRep.html#L25), the submodule of homogeneous polynomials of degree $n$ in $\mathbb C[X_0,X_1]$, on which $SL(2,\mathbb Z)$ acts by [`HeckeEis.binaryFormRepSL`](def/HeckeEis_BinaryFormRep.html#L61), i.e. $g$ substitutes $X_j \mapsto \sum_i g_{ij}X_i$. Let $W$ be a representation of the subgroup $\top \le SL(2,\mathbb Z)$ on the space of functions $X \to V_n$ which is assumed to be the induced one: $(W(g)f)(x) = g\cdot f(g^{-1}x)$ for all $g$, $f$, $x$. The conclusion is a conjunction of four assertions. First, $\dim_{\mathbb C}(X \to V_n) = (n+1)\,[SL(2,\mathbb Z):\Gamma_0(N)]$. Second, with $\nu_2$ the number of $x \in X$ fixed by $S$, $$2\nu_2\dim\ker(\rho_n(S)-1) + ([SL(2,\mathbb Z):\Gamma_0(N)]-\nu_2)(n+1) \le 2\dim\ker(W(S)-1),$$ the subtraction being truncated subtraction of naturals. Third, the same inequality with $S$ replaced by $ST$ and the factor $2$ by $3$, $\nu_3$ being the number of $ST$-fixed cosets. Fourth, the number of orbits of the subgroup of integer powers of $T$ on $X$ is at most $\dim\ker(W(T)-1)$.
--
--   This is the representation-theoretic input to the Eichler–Selberg style dimension count for spaces of modular forms of level $\Gamma_0(N)$: the three lower bounds measure the $S$-, $ST$- and $T$-invariants of the induced representation $\mathrm{Ind}_{\Gamma_0(N)}^{SL_2(\mathbb Z)}\mathrm{Sym}^n$ in terms of the elliptic points of order $2$ and $3$ and the cusps. It is used in the bound [`HeckeEis.finrank_coeffH1par_le_two_mul_dimFormula`](thm.html#HeckeEis.finrank_coeffH1par_le_two_mul_dimFormula) comparing a parabolic cohomology dimension with the classical dimension formula.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_le_finrank_fixed_induced_binaryFormRepSL.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.le_finrank_fixed_induced_binaryFormRepSL (N : ℕ) [NeZero N] (n : ℕ) (hn : Even n)
    (W : Representation ℂ (⊤ : Subgroup SL(2, ℤ)) (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℂ n)))
    (hW : ∀ (g : (⊤ : Subgroup SL(2, ℤ))) (f : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℂ n)) (x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N),
      W g f x = HeckeEis.binaryFormRepSL ℂ n (g : SL(2, ℤ)) (f (((g : SL(2, ℤ))⁻¹) • x))) :
    Module.finrank ℂ (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℂ n)) = (n + 1) * (CongruenceSubgroup.Gamma0 N).index ∧
    2 * (Nat.card {x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N // ModularGroup.S • x = x}
        * Module.finrank ℂ ↥(LinearMap.ker (HeckeEis.binaryFormRepSL ℂ n ModularGroup.S - 1)))
      + ((CongruenceSubgroup.Gamma0 N).index - Nat.card {x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N // ModularGroup.S • x = x}) * (n + 1)
      ≤ 2 * Module.finrank ℂ ↥(LinearMap.ker (W ⟨ModularGroup.S, Subgroup.mem_top _⟩ - 1)) ∧
    3 * (Nat.card {x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N // (ModularGroup.S * ModularGroup.T) • x = x}
        * Module.finrank ℂ ↥(LinearMap.ker (HeckeEis.binaryFormRepSL ℂ n (ModularGroup.S * ModularGroup.T) - 1)))
      + ((CongruenceSubgroup.Gamma0 N).index - Nat.card {x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N // (ModularGroup.S * ModularGroup.T) • x = x}) * (n + 1)
      ≤ 3 * Module.finrank ℂ ↥(LinearMap.ker (W ⟨ModularGroup.S * ModularGroup.T, Subgroup.mem_top _⟩ - 1)) ∧
    Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers ModularGroup.T) (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N))
      ≤ Module.finrank ℂ ↥(LinearMap.ker (W ⟨ModularGroup.T, Subgroup.mem_top _⟩ - 1)) := by sorry
