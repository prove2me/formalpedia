-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_deriv_archRealLift3_mul_eq_of_upperTriangular_equivariant
-- name    : LanglandsTunnell.CubicInduction.deriv_archRealLift3_mul_eq_of_upperTriangular_equivariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/f3de42d7-b486-5115-9e25-bca5f4288e7c
-- title:
--   First-order derivatives of an upper-triangular-equivariant function on GL₃
-- statement:
--   Fix $\nu : \mathrm{Fin}\,3 \to \mathbb{C}$ and a function $F$ on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$, i.e. on the general linear group of $3\times 3$ matrices over the adele ring of $\mathbb{Q}$ (`AdelicGL 3 (𝓞 ℚ) ℚ`), with values in $\mathbb{C}$. Here, for a real $3\times 3$ matrix $e$, [`WhittakerBlock.archRealLift3 e`](def/LanglandsTunnell_CubicInduction_ArchSmooth3.html#L18) denotes the adelic matrix obtained by placing the entries of $e$ at the archimedean component (through [`AutomorphicForm.archMatrixInclN`](def/AutomorphicForm_SmoothingKernel.html#L95) and [`AutomorphicForm.StandardKernel.ofReal`](def/AutomorphicForm_SmoothingKernel.html#L774)), regarded as an element of $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ when it is a unit and as $1$ otherwise. The hypothesis is left equivariance: for every $e : \mathrm{Fin}\,3 \to \mathrm{Fin}\,3 \to \mathbb{R}$ with $e_{ij} = 0$ whenever $j < i$ and $e_{ii} > 0$ for all $i$, and every $g$, one has $F(\mathrm{archRealLift3}(e)\,g) = \bigl(\prod_{a} (e_{aa})^{\nu_a + \rho_a}\bigr) F(g)$, the powers being complex powers of the real diagonal entries viewed in $\mathbb{C}$ and $\rho = (1,0,-1)$. The conclusion is the conjunction of two assertions: first, for all $i < j$ and all $g$, the derivative at $s = 0$ of $s \mapsto F(\mathrm{archRealLift3}(1 + sE_{ij})\,g)$ vanishes; second, for every index $c$ and every $g$, the derivative at $s = 0$ of $s \mapsto F(\mathrm{archRealLift3}(1 + sE_{cc})\,g)$ equals $(\nu_c + \rho_c) F(g)$. In both cases the matrix argument is written out as $a,b \mapsto \delta_{ab} + s\,[a = i \wedge b = j]$.
--
--   This is the infinitesimal form, along the elementary matrices of the upper-triangular group at the archimedean place, of left equivariance under the character $b \mapsto \prod_a b_{aa}^{\nu_a + \rho_a}$ with $\rho = (1,0,-1)$: the nilpotent directions act by zero and the diagonal directions by the scalars $\nu_a + \rho_a$. It feeds [`LanglandsTunnell.CubicInduction.casimir_eq_smul_of_upperTriangular_equivariant`](thm.html#LanglandsTunnell.CubicInduction.casimir_eq_smul_of_upperTriangular_equivariant), where the Casimir eigenvalue of such a function is computed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_deriv_archRealLift3_mul_eq_of_upperTriangular_equivariant.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.deriv_archRealLift3_mul_eq_of_upperTriangular_equivariant
    (ν : Fin 3 → ℂ) (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hB : ∀ e : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, j < i → e i j = 0) → (∀ i : Fin 3, 0 < e i i) →
      ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        F (WhittakerBlock.archRealLift3 e * g) =
          (∏ a : Fin 3, ((e a a : ℝ) : ℂ) ^ (ν a + (![1, 0, -1] : Fin 3 → ℂ) a)) * F g) :
    (∀ i j : Fin 3, i < j → ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      deriv (fun s : ℝ => F (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0) * g)) 0 = 0) ∧
    (∀ (c : Fin 3) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      deriv (fun s : ℝ => F (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + if a = c ∧ b = c then s else 0) * g)) 0 =
        (ν c + (![1, 0, -1] : Fin 3 → ℂ) c) * F g) := by sorry
