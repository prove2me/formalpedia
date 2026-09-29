-- Prove2me | Theorems.Thm_LocalGL2_exists_basis_heckeIndicator_zpow
-- name    : LocalGL2.exists_basis_heckeIndicator_zpow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/994d0581-9575-5210-89f9-12fff4a4d149
-- title:
--   Cartan basis of the Hecke algebra of GL₂(K)
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K$ (the field structure and the fraction-field identification being part of the data), let $\varpi \in R$ be irreducible whose image $\varpi \in K$ is nonzero, and let $R_0$ be any commutative ring. Write $U =$ `integralSubgroup R K` for the subgroup of $\mathrm{GL}_2(K)$ which is the range of the map $\mathrm{GL}_2(R) \to \mathrm{GL}_2(K)$ induced by $R \to K$. Assume `hfin`: for every $g \in \mathrm{GL}_2(K)$ the image of $U\cdot\{g\}$ in the coset space $\mathrm{GL}_2(K)/U$ is finite. Then the Hecke algebra `HeckeAlgebra` $U$ $R_0$ — the $R_0$-submodule of functions $\mathrm{GL}_2(K) \to R_0$ satisfying the predicate `IsHeckeFun` for $U$, i.e. invariance under left and right translation by $U$ together with a finiteness condition on the support modulo $U$ — admits an $R_0$-module basis indexed by the set of pairs $(m,n) \in \mathbb{Z} \times \mathbb{Z}$ with $m \le n$, whose vector at $(m,n)$ is the element `heckeIndicator`, namely the $\{0,1\}$-valued indicator function of the double coset $U\,g\,U$ for $g = (\mathrm{diag}(\varpi,1))^{m}\,(w\,\mathrm{diag}(\varpi,1)\,w)^{n}$, integral powers being taken in $\mathrm{GL}_2(K)$; here $\mathrm{diag}(\varpi,1)$ is `diagPi` and $w$ is `weylInt`, the image in $\mathrm{GL}_2(K)$ of the Weyl matrix over $R$, so that $w\,\mathrm{diag}(\varpi,1)\,w$ is `localRepInf`. The conclusion is a basis, not merely a spanning or independence assertion.
--
--   This is the Cartan (Iwasawa–Cartan) decomposition of $\mathrm{GL}_2$ over a discrete valuation ring in Hecke-algebraic form: the double-coset indicators $\mathbf 1_{U\,\mathrm{diag}(\varpi^m,\varpi^n)\,U}$ with $m \le n$ form an $R_0$-basis of the spherical Hecke algebra, the condition $m \le n$ removing the coincidence $\mathrm{diag}(\varpi^m,\varpi^n) \sim \mathrm{diag}(\varpi^n,\varpi^m)$. It supplies coordinates on the local Hecke algebra for the construction of matching Hecke operators at an inert prime and for the identification of orbital and twisted orbital integrals with their shadows.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LocalGL2_exists_basis_heckeIndicator_zpow.lean

import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckePair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Pointwise
open LocalGL2 HeckePair

theorem LocalGL2.exists_basis_heckeIndicator_zpow
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0) (hϖ : Irreducible ϖ)
    {R₀ : Type*} [CommRing R₀]
    (hfin : ∀ g : GL (Fin 2) K,
      (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K)) * {g}) :
        Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite) :
    ∃ b : Module.Basis {p : ℤ × ℤ // p.1 ≤ p.2} R₀ (HeckeAlgebra (integralSubgroup R K) R₀),
      ∀ p, b p = heckeIndicator R₀ (diagPi ϖ hϖ0 ^ p.1.1 * localRepInf ϖ hϖ0 ^ p.1.2) (hfin _) := by sorry
