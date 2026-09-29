-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isLocalZeta30ConvergentAbove_and_forall_exists_localZeta30_ne_zero_of_admissible_of_ne_zero
-- name    : LanglandsTunnell.CubicInduction.exists_isLocalZeta30ConvergentAbove_and_forall_exists_localZeta30_ne_zero_of_admissible_of_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/a75da5e9-2ca3-55f4-a039-3e6caad5ff64
-- title:
--   Non-vanishing of the local GL₃× GL₁ zeta integral
-- statement:
--   Let $\psi$ be an additive character of the adele ring of $\mathbb{Q}$ with values in $\mathbb{C}$, let $v$ be a finite place of $\mathbb{Q}$ (a height one prime of $\mathcal{O}_{\mathbb{Q}}$), and assume the local component $\psi_v$ at $v$, obtained by composing $\psi$ with the embedding of $\mathbb{Q}_v$ into the adeles at the single place $v$, is non-trivial. Let $W : GL_3(\mathbb{Q}_v) \to \mathbb{C}$ satisfy the $\psi_v$-Whittaker transformation law $W(u(x,y,z)g) = \psi_v(x+y)\,W(g)$ for all $x,y,z \in \mathbb{Q}_v$ and $g$, where $u(x,y,z)$ is the upper triangular unipotent matrix with entries $x$, $y$ above the diagonal and $z$ in the corner. Assume: $W$ is right invariant under some open subgroup $U_v \le GL_3(\mathbb{Q}_v)$; for every open subgroup $U_v$ there is a finite set $B$ of functions such that every element of the $\mathbb{C}$-span of the right translates of $W$ which is right $U_v$-invariant lies in the span of $B$; there is a homomorphism $\omega_v : \mathbb{Q}_v^\times \to \mathbb{C}^\times$ with $|\omega_v(z)| = 1$ and $W(z \cdot g) = \omega_v(z) W(g)$ for scalar matrices; and $W \neq 0$. Let $\chi : \mathbb{Q}_v^\times \to \mathbb{C}^\times$ be a homomorphism possessing a conductor exponent $c \in \mathbb{N}$, i.e. $\chi$ is trivial on the $c$-th higher unit group at $v$ and non-trivial on the $m$-th for every $m < c$. Then there exist $g \in GL_3(\mathbb{Q}_v)$ and $\sigma_0 \in \mathbb{R}$ such that, with respect to the multiplicative measure on $\mathbb{Q}_v^\times$ obtained by pulling back along $a \mapsto a$ the measure $|x|^{-1}\,dx$ built from the self-dual additive Haar measure at $v$, the function $a \mapsto W(\mathrm{diag}(a,1,1)\,g)\,\chi(a)\,|a|^{s-1}$ is integrable for every $s$ with $\operatorname{Re} s > \sigma_0$, and moreover for every $\sigma \in \mathbb{R}$ there is $s$ with $\operatorname{Re} s > \sigma$ for which the zeta integral $\int_{\mathbb{Q}_v^\times} W(\mathrm{diag}(a,1,1)\,g)\,\chi(a)\,|a|^{s-1}\,d^\times a$ is non-zero.
--
--   This is the local non-vanishing and convergence statement for the $GL_3 \times GL_1$ Rankin–Selberg zeta integral attached to an admissible Whittaker function at a finite place: some translate $g$ makes the integral converge on a right half-plane and take non-zero values arbitrarily far to the right. It supplies the input needed to choose normalising translates and to separate the contributions of the finite places in the cubic induction step, and is cited in the comparison of global zeta integrals with their local factors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_isLocalZeta30ConvergentAbove_and_forall_exists_localZeta30_ne_zero_of_admissible_of_ne_zero.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal MeasureTheory

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in
open scoped Classical in

theorem LanglandsTunnell.CubicInduction.exists_isLocalZeta30ConvergentAbove_and_forall_exists_localZeta30_ne_zero_of_admissible_of_ne_zero
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (v : HeightOneSpectrum (𝓞 ℚ)) (hψv : psiLoc ψ v ≠ 1)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn (psiLoc ψ v) W)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)))
    (ωv : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hωv : ∀ z : (v.adicCompletion ℚ)ˣ, ‖((ωv z : ℂˣ) : ℂ)‖ = 1)
    (hcen : ∀ (z : (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v),
      W (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((ωv z : ℂˣ) : ℂ) * W g)
    (hW0 : W ≠ 0)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : ∃ c : ℕ, LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v χ c) :
    letI := localBorel ℚ v
    ∃ (g : LocalGL3 v) (σ₀ : ℝ),
      IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ g σ₀ ∧
      ∀ σ : ℝ, ∃ s : ℂ, σ < s.re ∧
        localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ s g ≠ 0 := by sorry
