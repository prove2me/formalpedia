-- Prove2me | Theorems.Thm_ModularCurve_exists_addMonoidHom_torsion_proj_smul_eq_of_isIdempotentElem_tateModule_jH
-- name    : ModularCurve.exists_addMonoidHom_torsion_proj_smul_eq_of_isIdempotentElem_tateModule_jH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/3edf52a3-c68d-5ef2-a387-5d4bc9efa9c5
-- title:
--   Descent of a Hecke idempotent to J_H[p]
-- statement:
--   Let $p$ be a prime, let $M$ be a nonzero natural number, let $H \le (\mathbb{Z}/M)^\times$ and let $S$ be a set of natural numbers. Write $J =$ [`ModularCurve.JH M H`](def/ModularCurve_XH.html#L127), the group $\mathrm{Pic}^0$ of degree-zero divisors modulo principal divisors of the function field [`ModularCurve.xHFunctionFieldBar M H`](def/ModularCurve_XH.html#L123) over $\overline{\mathbb{Q}}$ (the field obtained by adjoining to $\overline{\mathbb{Q}}$ the coefficientwise images of the Laurent-series realisation of the level-$(M,H)$ function field), and let $J[p]$ denote the subgroup of elements annihilated by $p$. Let $\mathbb{T}$ be a commutative ring which is a $\mathbb{Z}_p$-algebra, equipped with a $\mathbb{T}$-module structure on the Tate module $T_pJ$ — sequences $(x_n)$ in $J$ with $p^n x_n = 0$ and $p\,x_{n+1} = x_n$ — compatible with the $\mathbb{Z}_p$-action. Suppose given $\mathrm{op} : \mathrm{Gen}(M,S) \to \mathbb{T}$, indexed by the generators $T_\ell$ ($\ell$ prime, $\ell \notin S$, $\ell \nmid M$), $U_q$ ($q$ prime, $q \mid M$) and $\langle d\rangle$ ($d \in (\mathbb{Z}/M)^\times$), such that $\mathrm{op}(g)$ acts on $T_pJ$ as [`ModularCurve.tateGenOpH`](def/ModularCurve_XHOperators.html#L99), the endomorphism induced on $T_pJ$ by the operator [`ModularCurve.genOpH M H S g`](def/ModularCurve_XHOperators.html#L80) of $J$, and such that $\mathbb{Z}_p[\mathrm{op}(g) : g]$ is all of $\mathbb{T}$. Let $e \in \mathbb{T}$ be idempotent. Then there exists an additive endomorphism $\varepsilon$ of $J[p]$ with the following four properties: evaluation at index $1$, [`TateModule.proj p J 1`](def/EllipticCurve_TateModule.html#L122), maps $T_pJ$ onto $J[p]$; whenever $v \in J[p]$ equals $\mathrm{proj}_1(x)$ for $x \in T_pJ$, one has $\varepsilon(v) = \mathrm{proj}_1(e \cdot x)$; for every additive subgroup $A \le J$ stable under all the operators [`ModularCurve.genOpH M H S g`](def/ModularCurve_XHOperators.html#L80), every $v \in J[p]$ lying in $A$ has $\varepsilon(v) \in A$; and for every $\mathbb{Z}/p$-bilinear form $b$ on $J[p]$ such that $b(x',y) = b(x,y')$ whenever $x',y' \in J[p]$ represent `genOpH` $g$ applied to $x,y$ respectively, one has $b(\varepsilon x, y) = b(x, \varepsilon y)$ for all $x,y$.
--
--   This is the bookkeeping step that transfers an idempotent of the Hecke algebra acting on the $p$-adic Tate module of $J_H(M)$ to an additive endomorphism of the $p$-torsion $J_H(M)[p]$, together with the two inheritance properties needed later: stability of subgroups stable under the Hecke and diamond operators, and self-adjointness for pairings for which those operators are self-adjoint. It is used in the analysis of the Néron-type data of $J_H(M)$ at $p$, in particular in the comparisons of cardinalities of corner subgroups with Weil-annihilator subgroups and in the construction of perfect pairings there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_addMonoidHom_torsion_proj_smul_eq_of_isIdempotentElem_tateModule_jH.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.exists_addMonoidHom_torsion_proj_smul_eq_of_isIdempotentElem_tateModule_jH
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    {𝕋 : Type} [CommRing 𝕋] [Algebra ℤ_[p] 𝕋] [Module 𝕋 (TateModule p (ModularCurve.JH M H))]
    [IsScalarTower ℤ_[p] 𝕋 (TateModule p (ModularCurve.JH M H))]
    (op : CohCarrier.Gen M S → 𝕋)
    (hop : ∀ (g : CohCarrier.Gen M S) (x : TateModule p (ModularCurve.JH M H)),
      op g • x = ModularCurve.tateGenOpH M H S p g x)
    (hgen : Algebra.adjoin ℤ_[p] (Set.range op) = ⊤)
    (e : 𝕋) (he : IsIdempotentElem e) :
    ∃ ε : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p) →+
        ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p),

      (∀ v : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p),
        ∃ x : TateModule p (ModularCurve.JH M H), TateModule.proj p (ModularCurve.JH M H) 1 x = v) ∧

      (∀ (x : TateModule p (ModularCurve.JH M H))
        (v : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)),
        (v : ModularCurve.JH M H) = TateModule.proj p (ModularCurve.JH M H) 1 x →
        ((ε v : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) :
          ModularCurve.JH M H) = TateModule.proj p (ModularCurve.JH M H) 1 (e • x)) ∧

      (∀ A : AddSubgroup (ModularCurve.JH M H),
        (∀ (g : CohCarrier.Gen M S) (x : ModularCurve.JH M H), x ∈ A → ModularCurve.genOpH M H S g x ∈ A) →
        ∀ v : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p),
          (v : ModularCurve.JH M H) ∈ A →
          ((ε v : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) :
            ModularCurve.JH M H) ∈ A) ∧

      (∀ b : LinearMap.BilinForm (ZMod p) ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p),
        (∀ (g : CohCarrier.Gen M S)
          (x y x' y' : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)),
          (x' : ModularCurve.JH M H) = ModularCurve.genOpH M H S g (x : ModularCurve.JH M H) →
          (y' : ModularCurve.JH M H) = ModularCurve.genOpH M H S g (y : ModularCurve.JH M H) → b x' y = b x y') →
        ∀ x y, b (ε x) y = b x (ε y)) := by sorry
