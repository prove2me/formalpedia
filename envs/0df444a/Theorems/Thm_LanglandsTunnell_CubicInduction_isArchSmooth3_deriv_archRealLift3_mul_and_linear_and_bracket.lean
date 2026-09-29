-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_isArchSmooth3_deriv_archRealLift3_mul_and_linear_and_bracket
-- name    : LanglandsTunnell.CubicInduction.isArchSmooth3_deriv_archRealLift3_mul_and_linear_and_bracket
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/29332cc9-08d8-5034-93a2-8f8a847eb177
-- title:
--   Smoothness, linearity and bracket law for archimedean left-flow derivatives
-- statement:
--   Let $\varphi : \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}}) \to \mathbb{C}$ be a function on the general linear group of the adele ring of $\mathbb{Q}$, and assume [`WhittakerBlock.IsArchSmooth3 φ`](def/LanglandsTunnell_CubicInduction_ArchSmooth3.html#L21), i.e. that for every $g$ the map sending a real $3\times 3$ array $e$ to $\varphi(g \cdot \mathtt{archRealLift3}\,e)$ is $C^\infty$ on the set of arrays with nonvanishing determinant; here $\mathtt{archRealLift3}\,e$ denotes the unit of $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ attached to the adelic matrix obtained by placing the real entries $e_{ij}$ at the archimedean place (and $1$ if that matrix fails to be a unit). For a real array $X$ write $L_X\varphi(g) := \frac{d}{ds}\big|_{s=0}\varphi\big(\mathtt{archRealLift3}(\delta + sX)\cdot g\big)$, with $\delta_{ab} = 1$ for $a=b$ and $0$ otherwise, the derivative being taken in Mathlib's sense. Three assertions are made. First, for every $X$ the function $g \mapsto L_X\varphi(g)$ again satisfies [`WhittakerBlock.IsArchSmooth3`](def/LanglandsTunnell_CubicInduction_ArchSmooth3.html#L21). Second, for all real arrays $X,Y$, real scalars $\alpha,\beta$ and all $g$, one has $L_{\alpha X + \beta Y}\varphi(g) = \alpha\, L_X\varphi(g) + \beta\, L_Y\varphi(g)$, the scalars being coerced into $\mathbb{C}$. Third, for all $X,Y$ and all $g$, the iterated derivatives satisfy $L_Y(L_X\varphi)(g) - L_X(L_Y\varphi)(g) = L_{[X,Y]}\varphi(g)$, where $[X,Y]$ is the commutator $X Y - Y X$ of $X$ and $Y$ viewed as matrices via `Matrix.of`; thus the left flows anti-represent $\mathfrak{gl}_3(\mathbb{R})$.
--
--   This is the elementary Lie calculus underlying the archimedean component of the theory: the left translation flows by $\delta + sX$ differentiate to derivations of the space of functions smooth at the infinite place, depend linearly on the direction, and satisfy the bracket relation of $\mathfrak{gl}_3$ up to sign. It supplies the differentiation rules used in the computation of the Casimir action, namely by [`LanglandsTunnell.CubicInduction.casimir_apply_eq_sum_deriv_archRealLift3_mul`](thm.html#LanglandsTunnell.CubicInduction.casimir_apply_eq_sum_deriv_archRealLift3_mul) and [`LanglandsTunnell.CubicInduction.casimir_eq_smul_of_deriv_archRealLift3_mul_eq`](thm.html#LanglandsTunnell.CubicInduction.casimir_eq_smul_of_deriv_archRealLift3_mul_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_isArchSmooth3_deriv_archRealLift3_mul_and_linear_and_bracket.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.isArchSmooth3_deriv_archRealLift3_mul_and_linear_and_bracket
    (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hsa : WhittakerBlock.IsArchSmooth3 φ) :
    (∀ X : Fin 3 → Fin 3 → ℝ,
      WhittakerBlock.IsArchSmooth3 (fun g => deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + s * X a b) * g)) 0)) ∧
    (∀ (X Y : Fin 3 → Fin 3 → ℝ) (α β : ℝ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + s * (fun a' b' => α * X a' b' + β * Y a' b') a b) * g)) 0
        = (α : ℂ) * deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + s * X a b) * g)) 0
          + (β : ℂ) * deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + s * Y a b) * g)) 0) ∧
    (∀ (X Y : Fin 3 → Fin 3 → ℝ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      deriv (fun t : ℝ => deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + s * X a b) * (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + t * Y a b) * g))) 0) 0
        - deriv (fun t : ℝ => deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + s * Y a b) * (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + t * X a b) * g))) 0) 0
        = deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + s * (fun a' b' => (Matrix.of X * Matrix.of Y - Matrix.of Y * Matrix.of X) a' b') a b) * g)) 0) := by sorry
