-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_polynomial_mul_localZeta30_eq_and_dual_of_isGL3PsiWhittakerFn
-- name    : LanglandsTunnell.CubicInduction.exists_polynomial_mul_localZeta30_eq_and_dual_of_isGL3PsiWhittakerFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/64ae543d-b250-5e35-8fcf-fef478dddbee
-- title:
--   Rationality in Nᵥ^{-s} of two GL₃ local zeta integrals
-- statement:
--   Let $\psi$ be a $\mathbb C$-valued additive character of the adele ring of $\mathbb Q$, let $v$ be a finite place of $\mathbb Q$ (a height one prime of $\mathcal O_{\mathbb Q}$) whose local component $\psi_v =$ `psiLoc` $\psi\,v$, the composite of $\psi$ with the inclusion of $\mathbb Q_v$ at $v$, is non-trivial, and let $W : GL_3(\mathbb Q_v) \to \mathbb C$ satisfy: the Whittaker law $W\big(u(x,y,z)g\big) = \psi_v(x+y)\,W(g)$ for all $x,y,z \in \mathbb Q_v$ and all $g$, where $u(x,y,z)$ is the upper triangular unipotent matrix with entries $x, y, z$; right invariance under some open subgroup of $GL_3(\mathbb Q_v)$; the finiteness condition that for every open subgroup $U_v$ there is a finite set $B$ of functions such that every element of the $\mathbb C$-span of the right translates of $W$ which is right $U_v$-invariant lies in the span of $B$; and $W(\mathrm{scalar}(z)g) = \omega_v(z)W(g)$ for a homomorphism $\omega_v : \mathbb Q_v^\times \to \mathbb C^\times$ all of whose values have absolute value $1$. Let $\tau : \mathbb Q_v^\times \to \mathbb C^\times$ admit a conductor exponent $c \in \mathbb N$, i.e. $\tau$ is trivial on the $c$-th higher unit group at $v$ while for each $m < c$ some unit of the $m$-th higher unit group has $\tau(u) \neq 1$. Write $\mu$ for the multiplicative measure $d^\times a = |a|^{-1}\,da$ obtained from the self-dual Haar measure $da$ on $\mathbb Q_v$ (restricted to $a \neq 0$) and pulled back along $\mathbb Q_v^\times \to \mathbb Q_v$, and $N_v$ for the absolute norm of $v$. Then there are real numbers $\sigma_0, \sigma_1$, independent of the point, such that for every $g \in GL_3(\mathbb Q_v)$: first, for every $s$ with $\operatorname{Re} s > \sigma_0$ the integrand $a \mapsto W\big(\mathrm{iotaGL}(\mathrm{diagUnitGL2}\,a)\,g\big)\,\tau(a)\,|a|^{s-1}$ is $\mu$-integrable, and there are polynomials $P, Q \in \mathbb C[X]$ with $Q \neq 0$ such that $Q(N_v^{-s})\cdot Z_0(s,g) = P(N_v^{-s})$ there, $Z_0$ being the integral of that integrand (`localZeta30`); secondly, for every $s$ with $\operatorname{Re} s > \sigma_1$ the corresponding integrand over $\mathbb Q_v^\times \times \mathbb Q_v$, built from the dual function $h \mapsto W(\mathrm{longWeyl3}\cdot {}^t h^{-1})$, the character $\tau^{-1}$ and the point $w'\,{}^t g^{-1}$, is integrable for $\mu$ times the self-dual measure, and there are polynomials $P, Q$ with $Q \neq 0$ such that $Q(N_v^{-s})\cdot Z_1(1-s,g) = P(N_v^{-s})$ for all $s$ with $\operatorname{Re}(1-s) > \sigma_1$, where $Z_1(1-s,g)$ is `localZetaDual31`, namely the $GL_3$ zeta integral with unipotent integration of the dual function against $\tau^{-1}$ at $1-s$ evaluated at $w'\,{}^t g^{-1}$. The polynomials depend on $g$ and on the choice of branch of $s$-dependence only through $N_v^{-s}$.
--
--   This is the local rationality statement for the $GL_3 \times GL_1$ zeta integral of a single smooth Whittaker function and for its dual integral, the non-archimedean input to the local functional equation in the Rankin–Selberg theory used in the cubic induction. It is obtained from the asymptotic expansion of Whittaker functions on the torus together with the convergence statement for the same two integrals, and feeds the comparison of global and local zeta integrals and the non-vanishing statements for `localZeta30`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_polynomial_mul_localZeta30_eq_and_dual_of_isGL3PsiWhittakerFn.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal MeasureTheory

theorem LanglandsTunnell.CubicInduction.exists_polynomial_mul_localZeta30_eq_and_dual_of_isGL3PsiWhittakerFn
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
      (IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W τ g σ₀ ∧
        ∃ P Q : Polynomial ℂ, Q ≠ 0 ∧ ∀ s : ℂ, σ₀ < s.re →
          Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) *
              localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W τ s g =
            P.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) ∧
      (IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
          (dualWhittakerFn3 W) τ⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
        ∃ P Q : Polynomial ℂ, Q ≠ 0 ∧ ∀ s : ℂ, σ₁ < (1 - s).re →
          Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) *
              localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
                W τ (1 - s) g =
            P.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) := by sorry
