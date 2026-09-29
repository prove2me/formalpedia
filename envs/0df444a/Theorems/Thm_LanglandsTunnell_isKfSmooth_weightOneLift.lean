-- Prove2me | Theorems.Thm_LanglandsTunnell_isKfSmooth_weightOneLift
-- name    : LanglandsTunnell.isKfSmooth_weightOneLift
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/009fcee6-45b8-56f3-bb41-1d966db83847
-- title:
--   Smoothness of the adelic weight-one lift
-- statement:
--   Let $n$ be a non-zero natural number and let $f : \mathfrak{H} \to \mathbb{C}$ be a function on the upper half-plane which is invariant under the weight-one slash action of $\Gamma_1(n)$: for every $\varepsilon \in \mathrm{SL}_2(\mathbb{Z})$ lying in `CongruenceSubgroup.Gamma1 n`, one has $f \mid[1]\,\varepsilon = f$, the image of $\varepsilon$ in $\mathrm{GL}_2(\mathbb{R})$ acting. Form the level ideal $N = (n)$ of $\mathcal{O}_{\mathbb{Q}}$ and the associated function `weightOneLift N f` on $\mathrm{GL}_2$ of the adele ring of $\mathbb{Q}$: its value at $g$ is $(f\mid[1]\,h_\infty)(i)\cdot \det(h_\infty)^1$, where $h_\infty =$ `ratArchGL2 h` is the real $\mathrm{GL}_2$-matrix obtained from the archimedean component of $h$ at the real place of $\mathbb{Q}$, for a chosen decomposition $g = \gamma\, h\, u$ with $\gamma \in \mathrm{GL}_2(\mathbb{Q})$ (embedded adelically), $u$ in the compact open subgroup `(productionPinsCompact ℚ).U N` of level $N$, the finite component of $h$ trivial and $h_\infty$ of positive determinant; the value is $0$ at points $g$ admitting no such decomposition. The assertion is that this function is `IsKfSmooth` over $\mathbb{Q}$, that is, its stabiliser under right translation inside the subgroup of adelic points with trivial archimedean component (the kernel of `AdelicLevel.glArch`) is an open subset of that subgroup.
--
--   This is the smoothness, i.e. right invariance under an open compact subgroup of the finite adelic points, of the adelic function attached to a weight-one form at level $\Gamma_1(n)$; no holomorphy, growth or cusp condition on $f$ is required or assumed. It is used in the dihedral weight-one constructions [`DihedralWeightOne.exists_smoothCuspRealizationAt_productionPinsGeneral_toFun_eq_weightOneLift_of_isPrimitiveForm`](thm.html#DihedralWeightOne.exists_smoothCuspRealizationAt_productionPinsGeneral_toFun_eq_weightOneLift_of_isPrimitiveForm) and [`DihedralWeightOne.weightOneLift_ne_zero_and_apply_mul_finEmbed_eq_of_isPrimitiveForm`](thm.html#DihedralWeightOne.weightOneLift_ne_zero_and_apply_mul_finEmbed_eq_of_isPrimitiveForm), which realise such a form as an adelic automorphic form; the existence of the required decompositions comes from [`AutomorphicForm.exists_mem_productionPinsCompact_U_mul_eq_rat`](thm.html#AutomorphicForm.exists_mem_productionPinsCompact_U_mul_eq_rat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_isKfSmooth_weightOneLift.lean

import Definitions.Def_AutomorphicForm_DihedralWeightOneLift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm UpperHalfPlane DihedralWeightOne
open scoped ModularForm MatrixGroups

theorem LanglandsTunnell.isKfSmooth_weightOneLift
    {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f) :
    IsKfSmooth ℚ (weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f) := by sorry
