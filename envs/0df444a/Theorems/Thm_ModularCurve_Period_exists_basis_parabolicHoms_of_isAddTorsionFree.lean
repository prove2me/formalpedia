-- Prove2me | Theorems.Thm_ModularCurve_Period_exists_basis_parabolicHoms_of_isAddTorsionFree
-- name    : ModularCurve.Period.exists_basis_parabolicHoms_of_isAddTorsionFree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/4b95a52a-d74a-57d1-ba7d-5f43023fa729
-- title:
--   Integral parabolic characters base-change to torsion-free rings
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb{Z})$ of finite index. For a commutative ring $R$, [`ModularCurve.Period.parabolicHoms R Γ R`](def/ModularCurve_PeriodMap.html#L62) denotes the $R$-submodule of $\mathrm{Hom}(\mathrm{Additive}\,\Gamma, R)$ — the additive group homomorphisms from $\Gamma$, written additively, to $R$ — consisting of those $\varphi$ with $\varphi(\gamma)=0$ for every $\gamma\in\Gamma$ whose underlying integral $2\times 2$ matrix satisfies $\operatorname{tr}(\gamma)^2=4$, i.e. $\operatorname{tr}(\gamma)=\pm 2$. The assertion is that there exist a natural number $n$ and a basis $b$ of the $\mathbb{Z}$-module [`ModularCurve.Period.parabolicHoms ℤ Γ ℤ`](def/ModularCurve_PeriodMap.html#L62) indexed by $\mathrm{Fin}\,n$ such that for every commutative ring $R$ that is additively torsion-free there is a basis $b^R$ of the $R$-module [`ModularCurve.Period.parabolicHoms R Γ R`](def/ModularCurve_PeriodMap.html#L62), again indexed by $\mathrm{Fin}\,n$, whose members are the base changes of those of $b$: for each $i$, the homomorphism $b^R_i : \mathrm{Additive}\,\Gamma \to R$ equals $b_i$ followed by the canonical additive map $\mathbb{Z}\to R$. In particular each such `parabolicHoms R Γ R` is free of the same rank $n$, with basis the image of a fixed integral basis.
--
--   This is the parabolic part $H^1_{\mathrm{par}}(\Gamma, R)$ of the first cohomology of $\Gamma$ with trivial coefficients, here realised concretely as the characters of $\Gamma$ vanishing on elements of trace $\pm 2$, and the statement says that over additively torsion-free coefficient rings this module is the base change of the integral one, uniformly in $R$ and with a single basis. It underlies the constructions of period lattices and modular symbols in the project, and is invoked by the results on Hecke and diamond operators acting on integral parabolic classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_Period_exists_basis_parabolicHoms_of_isAddTorsionFree.lean

import Definitions.Def_ModularCurve_PeriodMap
import Mathlib.LinearAlgebra.Basis.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.Period.exists_basis_parabolicHoms_of_isAddTorsionFree
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℤ (ModularCurve.Period.parabolicHoms ℤ Γ ℤ)),
      ∀ (R : Type*) [CommRing R] [IsAddTorsionFree R],
        ∃ bR : Module.Basis (Fin n) R (ModularCurve.Period.parabolicHoms R Γ R),
          ∀ i, (bR i : Additive Γ →+ R) = (Int.castAddHom R).comp (b i : Additive Γ →+ ℤ) := by sorry
