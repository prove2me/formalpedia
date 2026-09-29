-- Prove2me | Theorems.Thm_ModularCurve_exists_bilinForm_torsion_jH_nondegenerate_genOpH_selfAdjoint_galois
-- name    : ModularCurve.exists_bilinForm_torsion_jH_nondegenerate_genOpH_selfAdjoint_galois
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/8fed1887-1067-58fe-b54d-b15742037ae7
-- title:
--   Twisted Weil pairing as a bilinear form on J_H(M)[p]
-- statement:
--   Fix $M\ge 1$, a subgroup $H\le(\mathbb Z/M)^\times$, a set $S$ of natural numbers, and a prime $p$ with $p\mid M$. Write $J_H$ for the degree-zero divisor class group $\mathrm{Pic}^0$ (degree-zero divisors modulo principal ones) of the field obtained from the intermediate field [`ModularCurve.xHFunctionField M H`](def/ModularCurve_XH.html#L79) of $\mathbb{Q}$-rational Laurent series by the base change `laurentBaseChange` to $\overline{\mathbb Q}$, and let $V$ be its $p$-torsion subgroup, a $\mathbb Z/p$-module. The assertion is that there exists a $\mathbb Z/p$-bilinear form $b$ on $V$ with the following five properties. (i) and (ii): $b$ is non-degenerate on each side, i.e. $b(x,\cdot)=0$ forces $x=0$ and $b(\cdot,y)=0$ forces $y=0$. (iii) For every generator $g$ of [`CohCarrier.Gen M S`](def/CohCarrier_Inst.html#L13) — an operator label $T_\ell$ for $\ell$ prime, $\ell\notin S$, $\ell\nmid M$, or $U_q$ for $q$ prime with $q\mid M$, or $\langle d\rangle$ for $d\in(\mathbb Z/M)^\times$ — acting on $J_H$ by [`ModularCurve.genOpH`](def/ModularCurve_XHOperators.html#L80) (the Hecke operator `heckeOperatorHAlong` in the first two cases, the diamond endomorphism `diamondHBar` in the third), and all $x,y,x',y'\in V$ whose classes satisfy $x'=g\cdot x$ and $y'=g\cdot y$ in $J_H$, one has $b(x',y)=b(x,y')$. (iv) For every $\sigma\in\mathrm{Aut}(\overline{\mathbb Q}/\mathbb Q)$ and every $c$ coprime to $M$ such that $\sigma\zeta=\zeta^{c}$ for all $\zeta$ with $\zeta^{M}=1$, and all $x,y,x',y'\in V$ with $x'=\langle c\rangle(\sigma\cdot x)$ and $y'=\sigma\cdot y$ in $J_H$, one has $b(x',y')=c\,b(x,y)$ in $\mathbb Z/p$. (v) For every $\mathbb Z/p$-submodule $A\le V$ and every $x\in V$, if $b(x,y)=0$ for all $y$ annihilating $A$ on the left (that is, $b(a,y)=0$ for all $a\in A$), then $x\in A$. The Galois and Hecke clauses are stated via witnesses $x',y'$ in the torsion submodule whose classes are the images under the operators, rather than asserting that the operators preserve $V$.
--
--   This packages the $w_M$-twisted Weil pairing on the $p$-torsion of the modular Jacobian $J_H(M)$ as a single $\mathbb F_p$-valued bilinear form, with self-adjointness of the Hecke and diamond operators, the twisted Galois transformation law, and the double-annihilator (perfectness for submodules) property. It is the mod-$p$ interface used by the later statements about the Néron model of $J_H$ at $p$ and about the dual of the module of regular differentials in the ordinary case, and it is obtained from the multiplicative perfect pairing on $J_H$ with values in $\overline{\mathbb Q}^\times$ supplied by [`ModularCurve.exists_perfectPairing_nsmul_eq_zero_galois_heckeH_diamondH_forall_addSubgroup_eq_biannihilator`](thm.html#ModularCurve.exists_perfectPairing_nsmul_eq_zero_galois_heckeH_diamondH_forall_addSubgroup_eq_biannihilator).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_bilinForm_torsion_jH_nondegenerate_genOpH_selfAdjoint_galois.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

theorem ModularCurve.exists_bilinForm_torsion_jH_nondegenerate_genOpH_selfAdjoint_galois
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ) (p : ℕ) [Fact p.Prime] (hpM : p ∣ M) :
    ∃ b : LinearMap.BilinForm (ZMod p) ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p),
      (∀ x, (∀ y, b x y = 0) → x = 0) ∧ (∀ y, (∀ x, b x y = 0) → y = 0) ∧

      (∀ (g : CohCarrier.Gen M S) (x y x' y' : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)),
        (x' : ModularCurve.JH M H) = ModularCurve.genOpH M H S g (x : ModularCurve.JH M H) →
        (y' : ModularCurve.JH M H) = ModularCurve.genOpH M H S g (y : ModularCurve.JH M H) →
          b x' y = b x y') ∧

      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ) (hc : c.Coprime M),
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) →
        ∀ (x y x' y' : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)),
          (x' : ModularCurve.JH M H) = ModularCurve.diamondHBar M H (ZMod.unitOfCoprime c hc) (σ • (x : ModularCurve.JH M H)) →
          (y' : ModularCurve.JH M H) = σ • (y : ModularCurve.JH M H) →
            b x' y' = (c : ZMod p) • b x y) ∧

      (∀ (A : Submodule (ZMod p) ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p))
        (x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)),
        (∀ y, (∀ a ∈ A, b a y = 0) → b x y = 0) → x ∈ A) := by sorry
