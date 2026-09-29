-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_casimir_eq_smul_of_upperTriangular_equivariant
-- name    : LanglandsTunnell.CubicInduction.casimir_eq_smul_of_upperTriangular_equivariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/04278c62-686c-5c0d-9ad6-034bf0468ad1
-- title:
--   Casimir eigenvalues of a ν-equivariant function on GL₃
-- statement:
--   Fix $\nu : \mathrm{Fin}\,3 \to \mathbb{C}$ and a function $F$ on $GL_3$ of the adele ring of $\mathbb{Q}$ (with respect to $\mathcal{O}_{\mathbb{Q}}$) with values in $\mathbb{C}$. Two hypotheses are imposed. First, [`WhittakerBlock.IsArchSmooth3 F`](def/LanglandsTunnell_CubicInduction_ArchSmooth3.html#L21): for every $g$, the map sending a real $3\times 3$ matrix $e$ to $F(g \cdot \mathrm{archRealLift3}\,e)$ is $C^\infty$ on the set of $e$ with $\det e \neq 0$, where $\mathrm{archRealLift3}\,e$ is the adelic matrix obtained by placing $e$ at the archimedean place (and $1$ if that matrix fails to be invertible). Second, an equivariance: for every real $3\times 3$ matrix $e$ with $e_{ij}=0$ whenever $j<i$ and $e_{ii}>0$ for all $i$, and every $g$, one has $F(\mathrm{archRealLift3}\,e \cdot g) = \bigl(\prod_a e_{aa}^{\,\nu_a + \rho_a}\bigr) F(g)$ with $\rho = (1,0,-1)$ and complex powers of positive reals. Writing $\partial_{ij}\varphi(g)$ for the derivative at $s=0$ of $s \mapsto \varphi(g\cdot \mathrm{archRealLift3}(1 + s\,e_{ij}))$, and $C_1\varphi=\sum_i \partial_{ii}\varphi$, $C_2\varphi=\sum_{i,j}\partial_{ij}\partial_{ji}\varphi$, $C_3\varphi=\sum_{i,j,k}\partial_{ij}\partial_{jk}\partial_{ki}\varphi$, the conclusion is the conjunction of three equalities of functions: $C_1F = \bigl(\sum_a \nu_a\bigr)\cdot F$, $C_2F = \bigl(\sum_a \nu_a^2 - 2\bigr)\cdot F$, and $C_3F = \bigl(\sum_a \nu_a^3 + \sum_a \nu_a^2 - (\nu_0\nu_1+\nu_0\nu_2+\nu_1\nu_2) - 2\sum_a \nu_a - 3\bigr)\cdot F$.
--
--   This records the infinitesimal character of the principal series induced from the Borel with parameter $\nu$ for $GL_3(\mathbb{R})$, in the normalisation given by the three trace forms $C_1, C_2, C_3$ built from the right archimedean derivatives, with the shift $\rho = (1,0,-1)$ absorbed into the inducing character. It is used in the analysis of the leading coefficients of the smoothing submodule, where the Casimir scalars of the induced picture must be matched with those of the automorphic object.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_casimir_eq_smul_of_upperTriangular_equivariant.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem
LanglandsTunnell.CubicInduction.casimir_eq_smul_of_upperTriangular_equivariant
    (ν : Fin 3 → ℂ) (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hsa : WhittakerBlock.IsArchSmooth3 F)
    (hB : ∀ e : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, j < i → e i j = 0) → (∀ i : Fin 3, 0 < e i i) →
      ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        F (WhittakerBlock.archRealLift3 e * g) =
          (∏ a : Fin 3, ((e a a : ℝ) : ℂ) ^ (ν a + (![1, 0, -1] : Fin 3 → ℂ) a)) * F g) :
    WhittakerBlock.casimir1 F = (∑ a, ν a) • F ∧
    WhittakerBlock.casimir2 F = ((∑ a, ν a ^ 2) - 2) • F ∧
    WhittakerBlock.casimir3 F =
      ((∑ a, ν a ^ 3) + (∑ a, ν a ^ 2) - (ν 0 * ν 1 + ν 0 * ν 2 + ν 1 * ν 2) - 2 * (∑ a, ν a) - 3) • F := by sorry
