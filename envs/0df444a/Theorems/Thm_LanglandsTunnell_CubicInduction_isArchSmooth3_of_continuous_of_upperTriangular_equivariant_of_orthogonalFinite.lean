-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_isArchSmooth3_of_continuous_of_upperTriangular_equivariant_of_orthogonalFinite
-- name    : LanglandsTunnell.CubicInduction.isArchSmooth3_of_continuous_of_upperTriangular_equivariant_of_orthogonalFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/46636162-7248-500a-8d27-90f09021470c
-- title:
--   Archimedean smoothness from Iwasawa equivariance and orthogonal finiteness
-- statement:
--   Fix a tuple $\nu \in \mathbb{C}^3$ and a function $F$ on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$, the general linear group over the adele ring of $\mathbb{Q}$, with values in $\mathbb{C}$. Assume: (i) $F$ is continuous; (ii) for every real $3\times3$ array $t$ with $t_{ij}=0$ whenever $j<i$ and $t_{ii}>0$ for all $i$, and every $g$, one has $F(\,\mathrm{archRealLift3}(t)\cdot g) = \bigl(\prod_{a} t_{aa}^{\,\nu_a+\rho_a}\bigr)F(g)$ with $\rho=(1,0,-1)$, where [`WhittakerBlock.archRealLift3`](def/LanglandsTunnell_CubicInduction_ArchSmooth3.html#L18) places the real matrix at the archimedean component of the adeles and takes the resulting unit (and is $1$ if that matrix is not invertible), and the powers are complex powers of the diagonal entries; (iii) there is a finite set $s$ of $\mathbb{C}$-valued functions on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ such that for every $k'$ whose component at each height-one prime of $\mathcal{O}_{\mathbb{Q}}$ is the identity and whose archimedean component $k$ satisfies $k^{\mathsf{T}}k=1$ over the infinite adele ring, the right translate $g\mapsto F(gk')$ lies in the $\mathbb{C}$-span of $s$. The conclusion is [`WhittakerBlock.IsArchSmooth3 F`](def/LanglandsTunnell_CubicInduction_ArchSmooth3.html#L21): for every $g$ the map $e \mapsto F(g\cdot \mathrm{archRealLift3}(e))$ is $C^\infty$ on the set of real $3\times3$ arrays $e$ with $\det e \neq 0$.
--
--   This is the standard passage from left equivariance under the upper-triangular real group together with right finiteness under the orthogonal group at infinity to smoothness in the archimedean variable, obtained from the smooth Iwasawa decomposition and the fact that a continuous, finitely-spanned function on the orthogonal group is polynomial. It feeds the construction of the induced-picture package used in the cubic induction step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_isArchSmooth3_of_continuous_of_upperTriangular_equivariant_of_orthogonalFinite.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.isArchSmooth3_of_continuous_of_upperTriangular_equivariant_of_orthogonalFinite
    (ν : Fin 3 → ℂ) (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hcont : Continuous F)
    (heq : ∀ t : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, j < i → t i j = 0) → (∀ i : Fin 3, 0 < t i i) →
        ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, F (WhittakerBlock.archRealLift3 t * g) =
          (∏ a : Fin 3, ((t a a : ℝ) : ℂ) ^ (ν a + (![1, 0, -1] : Fin 3 → ℂ) a)) * F g)
    (hfin : ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k' = 1) → archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3 →
          (fun g => F (g * k')) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) :
    WhittakerBlock.IsArchSmooth3 F := by sorry
