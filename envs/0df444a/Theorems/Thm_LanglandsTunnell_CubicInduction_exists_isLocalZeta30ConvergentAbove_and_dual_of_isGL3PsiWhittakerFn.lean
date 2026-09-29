-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isLocalZeta30ConvergentAbove_and_dual_of_isGL3PsiWhittakerFn
-- name    : LanglandsTunnell.CubicInduction.exists_isLocalZeta30ConvergentAbove_and_dual_of_isGL3PsiWhittakerFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/5c549989-094d-5ce3-ae27-d5cd100346a0
-- title:
--   Convergence of local GL₃× GL₁ zeta integrals and their duals
-- statement:
--   Let $\psi$ be an additive character of the adele ring of $\mathbb{Q}$ with values in $\mathbb{C}$, let $v$ be a finite place of $\mathbb{Q}$, and suppose the local component $\psi_v =$ `psiLoc ψ v` (the composite of $\psi$ with the inclusion of $\mathbb{Q}_v$ at $v$) is non-trivial. Let $W : GL_3(\mathbb{Q}_v) \to \mathbb{C}$ satisfy the Whittaker law $W(\mathrm{u}(x,y,z)g) = \psi_v(x+y)W(g)$ for the upper unipotent matrix with entries $x,y,z$; assume $W$ is invariant under right translation by some open subgroup; assume that for every open subgroup $U_v$ there is a finite set $B$ of functions such that every element of the span of the right translates of $W$ which is right $U_v$-invariant lies in the $\mathbb{C}$-span of $B$; assume $W(\mathrm{diag}(z,z,z)g) = \omega_v(z)W(g)$ for a character $\omega_v$ of $\mathbb{Q}_v^\times$ of absolute value one; and let $\tau : \mathbb{Q}_v^\times \to \mathbb{C}^\times$ admit a conductor exponent $c$, i.e. $\tau$ is trivial on the $c$-th higher unit group and non-trivial on the $m$-th one for every $m < c$. Then there are reals $\sigma_0, \sigma_1$, independent of the point, such that for every $g \in GL_3(\mathbb{Q}_v)$: for all $s$ with $\operatorname{Re} s > \sigma_0$ the function $a \mapsto W(\iota(\mathrm{diag}(a,1))g)\,\tau(a)\,|a|_v^{s-1}$ is integrable on $\mathbb{Q}_v^\times$ for the pullback along $a \mapsto a$ of the multiplicative measure attached to the self-dual Haar measure at $v$ (its restriction to the non-zero elements with density $|x|_v^{-1}$), $\iota$ being the upper-left block embedding $GL_2 \hookrightarrow GL_3$; and for all $s$ with $\operatorname{Re} s > \sigma_1$ the function $(a,x) \mapsto W\bigl(\mathtt{longWeyl3}\cdot {}^{t}(\iota(\mathrm{diag}(a,1))\,n_{21}(x)\,w'\,{}^{t}g^{-1})^{-1}\bigr)\,\tau(a)^{-1}\,|a|_v^{s-1}$ is integrable for the product of that multiplicative measure with the self-dual Haar measure on $\mathbb{Q}_v$, where $n_{21}(x)$ is the lower unipotent matrix with entry $x$ in position $(2,1)$ and $w'$ is the permutation matrix interchanging the second and third coordinates.
--
--   This is the local absolute-convergence statement for the $GL_3 \times GL_1$ zeta integral of a smooth Whittaker function and for the companion integral of its dual function, in the form used in the Rankin–Selberg theory of Jacquet–Piatetski-Shapiro–Shalika. It underlies the local functional equation and meromorphic continuation statements, and is cited in the construction of the cubic-induction Hecke datum, in the shell-by-shell summation of the zeta integral over powers of a uniformiser, and in the integrability of the dual part of a gauge-majorised cubic induction datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_isLocalZeta30ConvergentAbove_and_dual_of_isGL3PsiWhittakerFn.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal MeasureTheory

theorem LanglandsTunnell.CubicInduction.exists_isLocalZeta30ConvergentAbove_and_dual_of_isGL3PsiWhittakerFn
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
    (τ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hτ : ∃ c : ℕ, LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v τ c) :
    letI := localBorel ℚ v
    ∃ σ₀ σ₁ : ℝ,
      ∀ g : LocalGL3 v,
      IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
        W τ g σ₀ ∧
      IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
        (dualWhittakerFn3 W)
        τ⁻¹ (weylPrime3 * transposeInv3 g) σ₁ := by sorry
