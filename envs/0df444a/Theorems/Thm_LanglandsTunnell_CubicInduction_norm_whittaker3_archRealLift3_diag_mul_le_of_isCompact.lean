-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact
-- name    : LanglandsTunnell.CubicInduction.norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/d94745aa-0d79-5a2c-a4c6-becd5bf88dfb
-- title:
--   Uniform moderate-growth bound for the GL₃ Whittaker coefficient on the diagonal
-- statement:
--   Let $N$ be a natural number and let $u$ be a complex-valued function on $\mathrm{GL}_3$ of the adele ring of $\mathbb{Q}$. For a finite list $w$ of pairs of indices in $\mathrm{Fin}\,3 \times \mathrm{Fin}\,3$ write $u_w$ for the iterated archimedean directional derivative of $u$ obtained by folding `WhittakerBlock.archDeriv`, where $(\mathrm{archDeriv}\,i\,j\,\varphi)(g)$ is the derivative at $s=0$ of $s \mapsto \varphi(g\cdot \mathrm{archRealLift3}(1 + s\,e_{ij}))$, the lift sending a real matrix to its image at the archimedean places (and to $1$ if that image is not a unit). Assume each $u_w$ is continuous, and that for each $w$ there is a constant $C$ with $\|u_w(g)\| \le C\,\mathrm{gauge3}_{\mathbb{Q}}(g)^N$ for all $g$, where $\mathrm{gauge3}$ is the maximum of $1$ and the product of the archimedean gauge $1 + \sum_{w \mid \infty} \mathrm{matrixSize}$ of the archimedean components with the finite gauge $\prod_v \mathrm{matrixSupSize}$ of the components at the finite places. Then for every compact set $K$ of adelic matrices there is a real constant $C$ such that for all $k \in K$ and all reals $y_1, y_2 > 0$, the Whittaker coefficient of $u$, namely the triple integral of $u(\mathrm{upperUnipotent3}(x,y,z)\,g)\,\psi_{\mathbb{Q}}(-(x+y))$ against the additive adelic Haar measure conditioned on the adelic box (a probability measure) with $\psi_{\mathbb{Q}}$ the standard additive character, evaluated at $g = \mathrm{archRealLift3}(\mathrm{diag}(y_1y_2, y_2, 1))\cdot k$, has norm at most $C\,(\max(y_1,1)\max(y_2,1)\max(y_1^{-1},1)\max(y_2^{-1},1))^N$.
--
--   This is the a priori moderate-growth estimate for the $\mathrm{GL}_3$ Whittaker coefficient restricted to the diagonal torus, uniform over compact sets of right translates: the polynomial growth assumption on $u$ and all its archimedean derivatives is transferred, through an integral over a compact box against a probability measure, to a bound polynomial in $y_1^{\pm 1}, y_2^{\pm 1}$. It is the growth input for the results that extract asymptotic expansions of the diagonal Whittaker function from the Casimir relations, in particular the leading-exponent and regular-singular-system statements used later in the cubic induction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem
LanglandsTunnell.CubicInduction.norm_whittaker3_archRealLift3_diag_mul_le_of_isCompact
    (N : ℕ) (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hcw : ∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w))
    (hgr : ∀ w : List (Fin 3 × Fin 3), ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ‖List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w g‖ ≤ C * gauge3 ℚ g ^ N) :
    ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
      ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ u
          (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k)‖ ≤
        C * (max y₁ 1 * max y₂ 1 * max y₁⁻¹ 1 * max y₂⁻¹ 1) ^ N := by sorry
