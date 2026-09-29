-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_finite_fixedPoints_frobSp_comp_self
-- name    : ModularCurve.JZeroNeronObjectAtP.finite_fixedPoints_frobSp_comp_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/60bd0908-e1ac-5778-b4c1-fce889eb8b59
-- title:
--   Finiteness of the fixed points of frobSp²
-- statement:
--   Fix natural numbers $N_0$ and $p$ with $N_0 \neq 0$, with $p$ prime and nonzero, and assume $p \nmid N_0$. Let $A$ be a valuation subring of an algebraic closure $\overline{\mathbb{Q}}$ of $\mathbb{Q}$ lying over $p$, in the sense that the image of $p$ in $\overline{\mathbb{Q}}$ is a nonunit of $A$; write $\kappa = \mathrm{ResidueField}\,A$. Let $\Lambda$ be a datum of type `LevelData N₀ p A`, consisting of a section $\sigma_A$ of `base p` from $\operatorname{Spec} A$ compatible with the generic point, a scheme $X$ over `base p` with a relative group law, and bijections identifying $\mathrm{JZero}\,N_0$ (the degree-zero class group of the level-$N_0$ modular function field over $\overline{\mathbb{Q}}$) with the generic-fibre sections of $X$ and $\mathrm{JZeroC}\,\kappa\,N_0$ with the sections over the residual point. Let $O$ be a datum of type `JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ`: a commutative relative group scheme $g : G \to$ `base p` which is smooth, separated, locally of finite type, quasi-compact and surjective with preconnected fibres, together with a Galois- and Hecke-equivariant identification of $\mathrm{JZero}(N_0 p)$ with its generic-fibre sections, flatness and surjectivity of multiplication by each $n > 0$, properness of the generic fibre, a toric rank and further data and axioms. Then the set of fixed points of the self-map $O.\mathrm{frobSp}$ composed with itself is finite.
--
--   The specialisation map $O.\mathrm{frobSp}$ plays the role of the Frobenius pushforward on the level-$N_0$ special-fibre class group over the residue field at $A$; fixed points of its square are the classes rational over the field with $p^2$ elements, and their finiteness is the source of the finite sets of coset representatives used later. It is invoked in the analysis of the toric and finite parts of the Néron object, for instance in [`ModularCurve.JZeroNeronObjectAtP.exists_nsmul_mem_toricPts_of_mem_finPts`](thm.html#ModularCurve.JZeroNeronObjectAtP.exists_nsmul_mem_toricPts_of_mem_finPts) and [`ModularCurve.JZeroNeronObjectAtP.exists_isOpenImmersion_torus_kerPair_degeneracyHom`](thm.html#ModularCurve.JZeroNeronObjectAtP.exists_isOpenImmersion_torus_kerPair_degeneracyHom).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_finite_fixedPoints_frobSp_comp_self.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_ToricDescentData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP
open ModularCurve

theorem ModularCurve.JZeroNeronObjectAtP.finite_fixedPoints_frobSp_comp_self
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) :
    (Function.fixedPoints (O.frobSp ∘ O.frobSp)).Finite := by sorry
