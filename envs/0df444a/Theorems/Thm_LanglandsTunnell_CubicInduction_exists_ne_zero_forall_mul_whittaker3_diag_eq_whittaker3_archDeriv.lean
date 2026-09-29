-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_ne_zero_forall_mul_whittaker3_diag_eq_whittaker3_archDeriv
-- name    : LanglandsTunnell.CubicInduction.exists_ne_zero_forall_mul_whittaker3_diag_eq_whittaker3_archDeriv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/e1b972a0-cbe9-53b0-92aa-653a58e4684a
-- title:
--   Simple-root derivatives of the GL₃ Whittaker coefficient at a diagonal point
-- statement:
--   There is a non-zero complex number $\lambda$, fixed once and for all independently of everything that follows, with the following property. Let $\varphi : \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}}) \to \mathbb{C}$ be a function such that: (i) [`WhittakerBlock.IsArchSmooth3 φ`](def/LanglandsTunnell_CubicInduction_ArchSmooth3.html#L21) holds, i.e. for every adelic point $g$ the map sending a real $3 \times 3$ matrix $e$ to $\varphi(g \cdot \mathrm{archRealLift3}(e))$, where $\mathrm{archRealLift3}$ places $e$ at the archimedean place (and is $1$ when the resulting adelic matrix is not invertible), is $C^{\infty}$ on the set of $e$ with $\det e \neq 0$; (ii) for every finite word $w$ of pairs $(i,j) \in \mathrm{Fin}\,3 \times \mathrm{Fin}\,3$, the iterated derivative of $\varphi$ obtained by folding `WhittakerBlock.archDeriv` over $w$ is continuous, where $\mathrm{archDeriv}\,i\,j\,\psi(g)$ is the derivative at $s = 0$ of $s \mapsto \psi\bigl(g \cdot \mathrm{archRealLift3}(1 + s E_{ij})\bigr)$ (the empty word gives continuity of $\varphi$ itself); (iii) $\varphi(\gamma g) = \varphi(g)$ for all $\gamma \in \mathrm{GL}_3(\mathbb{Q})$, embedded by `globalPointsGL`, and all $g$. Then for all reals $y_1, y_2 > 0$, writing $t = \mathrm{archRealLift3}(\mathrm{diag}(y_1y_2, y_2, 1))$ and $W(\Phi)(g) = \int\!\!\int\!\!\int \Phi\bigl(u(x,y,z)\,g\bigr)\,\psi_{\mathbb{Q}}(-(x+y))$ for the standard additive character $\psi_{\mathbb{Q}}$ of $\mathbb{A}_{\mathbb{Q}}$, the upper unipotent matrix $u(x,y,z)$ with entries $1,x,z;0,1,y;0,0,1$, and each of the three integrations against the conditioning of adelic additive Haar measure to the adelic box (fundamental domain at the infinite places times the integral finite adeles), one has $$\lambda\, y_1\, W(\varphi)(t) = W(\mathrm{archDeriv}\,0\,1\,\varphi)(t), \qquad \lambda\, y_2\, W(\varphi)(t) = W(\mathrm{archDeriv}\,1\,2\,\varphi)(t).$$
--
--   This is the archimedean raising relation for Whittaker coefficients on $\mathrm{GL}_3$: conjugation by the diagonal element $\mathrm{diag}(y_1y_2,y_2,1)$ scales the two simple-root one-parameter subgroups by $y_1$ and $y_2$, and the Whittaker coefficient transforms under the maximal unipotent subgroup by the character, so differentiating along a simple root multiplies the coefficient by the corresponding torus coordinate times the derivative $\lambda$ of the archimedean component of $\psi_{\mathbb{Q}}$ at the origin. It is used to obtain the second-order relation and vanishing of the corner derivative, and the decay estimate for sums of translates of Whittaker coefficients along the diagonal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_ne_zero_forall_mul_whittaker3_diag_eq_whittaker3_archDeriv.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem
LanglandsTunnell.CubicInduction.exists_ne_zero_forall_mul_whittaker3_diag_eq_whittaker3_archDeriv :
    ∃ lam : ℂ, lam ≠ 0 ∧ ∀ (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), WhittakerBlock.IsArchSmooth3 φ →
      (∀ w : List (Fin 3 × Fin 3),
        Continuous (List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) φ w)) →
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = φ g) →
      ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
      lam * (y₁ : ℂ) * whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ φ
          (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0)) =
        whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ (WhittakerBlock.archDeriv 0 1 φ)
          (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0)) ∧
      lam * (y₂ : ℂ) * whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ φ
          (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0)) =
        whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ (WhittakerBlock.archDeriv 1 2 φ)
          (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0)) := by sorry
