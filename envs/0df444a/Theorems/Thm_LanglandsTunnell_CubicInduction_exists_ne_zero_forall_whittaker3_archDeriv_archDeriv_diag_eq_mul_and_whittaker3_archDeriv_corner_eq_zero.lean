-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_ne_zero_forall_whittaker3_archDeriv_archDeriv_diag_eq_mul_and_whittaker3_archDeriv_corner_eq_zero
-- name    : LanglandsTunnell.CubicInduction.exists_ne_zero_forall_whittaker3_archDeriv_archDeriv_diag_eq_mul_and_whittaker3_archDeriv_corner_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/b8085eb3-b496-5814-a756-0da3c02820be
-- title:
--   Two archimedean derivative identities for GL₃ Whittaker coefficients
-- statement:
--   There exists a non-zero complex number $\lambda$, independent of everything that follows, with the following property. Let $\varphi$ be a complex-valued function on $\mathrm{GL}_3$ of the adele ring of $\mathbb{Q}$ such that: (i) [`WhittakerBlock.IsArchSmooth3`](def/LanglandsTunnell_CubicInduction_ArchSmooth3.html#L21) holds, i.e. for every $g$ the map $e \mapsto \varphi(g \cdot \mathtt{archRealLift3}\,e)$ from real $3\times 3$ matrices is $C^\infty$ on the locus where $\det e \neq 0$, the lift `archRealLift3` sending a real matrix to the corresponding adelic matrix at the archimedean place (and to $1$ when it is not invertible); (ii) every derivative word in $\varphi$ is continuous, where a word is a list $w$ of pairs $(i,j)$ of indices in $\mathrm{Fin}\,3$ acted on by iterating, from the right, the operators $\mathtt{archDeriv}\,i\,j\,\psi : g \mapsto \frac{d}{ds}\psi\bigl(g \cdot \mathtt{archRealLift3}(1 + s E_{ij})\bigr)\big|_{s=0}$; (iii) $\varphi$ is left invariant under the image of $\mathrm{GL}_3(\mathbb{Q})$ under `globalPointsGL`. Let $y_1, y_2 > 0$ and let $a$ be the archimedean lift of $\mathrm{diag}(y_1y_2, y_2, 1)$. Write $W_\Phi$ for the Whittaker coefficient $g \mapsto \int\!\!\int\!\!\int \Phi(u(x,y,z)\,g)\,\psi_{\mathbb{Q}}(-(x+y))$, the integrals being against the adelic additive Haar measure conditioned on the adelic box (a fundamental domain for the lattice at the infinite place times the integral finite adeles), with $u(x,y,z)$ the upper unipotent matrix with entries $x,y,z$, $\psi_{\mathbb{Q}}$ the standard additive character of the adeles of $\mathbb{Q}$, and the remaining data of the carrier pins (empty set, trivial level subgroups, unit uniformisers) irrelevant to this integral. Then $$W_{\mathtt{archDeriv}\,0\,1(\mathtt{archDeriv}\,1\,2\,\varphi)}(a) = \lambda^2\,y_1\,y_2\,W_\varphi(a), \qquad W_{\mathtt{archDeriv}\,0\,2\,\varphi}(a) = 0.$$
--
--   This is the root-coordinate computation, in the style of Jacquet's analysis of Whittaker functions on Chevalley groups, of how the archimedean raising operators attached to the simple roots and to the highest root act on a Whittaker coefficient restricted to the diagonal torus: the composite of the two simple-root operators multiplies it by $\lambda^2 y_1 y_2$, while the highest-root operator annihilates it. It is used, via the quantised minor built from these operators, in [`LanglandsTunnell.CubicInduction.eq_zero_of_read_signProjection_of_separating_stable_submodule`](thm.html#LanglandsTunnell.CubicInduction.eq_zero_of_read_signProjection_of_separating_stable_submodule), where the non-vanishing of the resulting factor on the torus forces a Whittaker coefficient to vanish.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_ne_zero_forall_whittaker3_archDeriv_archDeriv_diag_eq_mul_and_whittaker3_archDeriv_corner_eq_zero.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.exists_ne_zero_forall_whittaker3_archDeriv_archDeriv_diag_eq_mul_and_whittaker3_archDeriv_corner_eq_zero :
    ∃ lam : ℂ, lam ≠ 0 ∧ ∀ (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), WhittakerBlock.IsArchSmooth3 φ →
      (∀ w : List (Fin 3 × Fin 3),
        Continuous (List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) φ w)) →
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = φ g) →
      ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
      whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ (WhittakerBlock.archDeriv 0 1 (WhittakerBlock.archDeriv 1 2 φ))
          (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0)) =
        lam ^ 2 * (y₁ : ℂ) * (y₂ : ℂ) *
          whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ φ
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0)) ∧
      whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ (WhittakerBlock.archDeriv 0 2 φ)
          (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0)) = 0 := by sorry
