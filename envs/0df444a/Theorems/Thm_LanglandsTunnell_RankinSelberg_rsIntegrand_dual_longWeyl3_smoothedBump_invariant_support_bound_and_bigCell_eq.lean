-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_rsIntegrand_dual_longWeyl3_smoothedBump_invariant_support_bound_and_bigCell_eq
-- name    : LanglandsTunnell.RankinSelberg.rsIntegrand_dual_longWeyl3_smoothedBump_invariant_support_bound_and_bigCell_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/d840472b-dd40-56f9-89ab-e2e9d55ccbb0
-- title:
--   Local dual Rankin–Selberg integrand of a smoothed bump vector
-- statement:
--   Let $p$ be a nonzero prime of $\mathcal O_{\mathbb Q}$ with completion $\mathbb Q_p$, let $\psi$ be the standard local additive character `psiLocal ℚ p`, let $\nu$ be the self-dual measure `selfDualHaarAt ℚ p`, and write $\hat\varphi(y)=\int\varphi(x)\,\psi^{-1}(xy)\,d\nu(x)$. Fix $w_{0,p}\in GL_2(\mathbb Q_p)$ with matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$, characters $\omega,\theta:\mathbb Q_p^\times\to\mathbb C^\times$, and $f\in\mathbb N$. Let $W_0:GL_3(\mathbb Q_p)\to\mathbb C$ satisfy $W_0(n(x,y,z)g)=\psi^{-1}(x+y)W_0(g)$ for the upper unipotent $n(x,y,z)$, be right invariant under some open subgroup, satisfy $W_0(tI_3\,h)=\omega(t)W_0(h)$, be right invariant under the set of $k\in GL_3(\mathbb Q_p)$ with $k,k^{-1}$ of entries of valuation $\le 1$ and $v(k_{20}),v(k_{21}),v(k_{22}-1)\le |p|^{f}$ (that is, $\le \exp(-f)$), and, along $\iota(h)=\mathrm{diag}(h,1)$, be right invariant under [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤`](def/AdelicDock_LocalEmbedding.html#L178) (the preimage under the local embedding of the adelic level-one group at the unit ideal), vanish unless $h=n(x)k$ with $k$ in that group, and satisfy $W_0(\iota 1)=1$. Let $w:GL_2(\mathbb Q_p)\to\mathbb C$ satisfy $w(n(x)g)=\psi(x)w(g)$, be right invariant under an open subgroup, and have central character $\theta$. Let $\varphi,\varphi_1$ be locally constant of compact support with: $\hat\varphi(t)=\theta(t)$ for units $t$ with $v(t)=1$; $\hat\varphi(y)=0$ when $v(y)\ne 1$; $\hat\varphi_1(ty)=\omega(t)\hat\varphi_1(y)$ for such $t$; and $\hat\varphi_1(y)\ne0\Rightarrow v(y)\le\exp(-f)$. Put $W_3(X)=\iint W_0(X\,w_\ell\,n(u,0,y))\,\varphi(u)\varphi_1(y)\,d\nu\,d\nu$ with $w_\ell$ the long Weyl element, $\widetilde W_3(g)=W_3(w_\ell\,{}^t g^{-1})$, and $\Phi(g)=\widetilde W_3(\iota g)\cdot\bigl(\|\det g\|\cdot w(w_{0,p}\,{}^tg^{-1})\bigr)$ on $GL_2(\mathbb Q_p)$, the groups carrying their Borel structures. Then: $\Phi$ is measurable; $\Phi(n(x)g)=\Phi(g)$ for all $x,g$; $\Phi(g)\ne0$ implies $g=n(x)u$ with $u\in$ `localLevelOne (𝓞 ℚ) ℚ p ⊤`; $\Phi$ is bounded on that subgroup; and for all $y,x\in\mathbb Q_p$ and units $a,d$, the indicator of that subgroup applied to $\Phi$ at $n(y)\,\mathrm{diag}(d,a)\,\bar n(x)$ (with $\bar n(x)$ lower unipotent) equals $\mathbf 1_{v(y)\le1}$ times $\omega(ad^{-1})\,\hat\varphi_1(x)\,w(w_{0,p}\,\mathrm{diag}(ad^{-1},1)\,n(-x))$ if $v(a)=v(d)=1$, and $0$ otherwise.
--
--   This is the pointwise input for the computation of the dual local $GL_3\times GL_2$ Rankin–Selberg integral of a smoothed bump vector: the five clauses give measurability, left invariance under the unipotent radical, support in $N_2\cdot GL_2(\mathbb Z_p)$, boundedness on the maximal compact, and the value on the big Bruhat cell. It is cited by `exists_pos_forall_rsLocalIntegral_dual_longWeyl3_smoothedBump_eq_mul_setIntegral_unitShell`, where the quotient integral is unfolded and reduced to an integral over the unit shell.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_rsIntegrand_dual_longWeyl3_smoothedBump_invariant_support_bound_and_bigCell_eq.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_ArchDerivCasimir

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors

open scoped Classical in

open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.rsIntegrand_dual_longWeyl3_smoothedBump_invariant_support_bound_and_bigCell_eq
    (p : HeightOneSpectrum (𝓞 ℚ))
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (ω θ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (f : ℕ)
    (W₀ : LocalGL3 p → ℂ)
    (hW₀law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₀)
    (hW₀sm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 p, W₀ (g * k) = W₀ g)
    (hω : ∀ (t : (p.adicCompletion ℚ)ˣ) (h : LocalGL3 p),
      W₀ (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω t : ℂˣ) : ℂ) * W₀ h)
    (hK1 : ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ p f, ∀ g : LocalGL3 p, W₀ (g * k) = W₀ g)
    (hbumpK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ h : GL (Fin 2) (p.adicCompletion ℚ), W₀ (iotaGL (h * k)) = W₀ (iotaGL h))
    (hbumpS : ∀ h : GL (Fin 2) (p.adicCompletion ℚ), W₀ (iotaGL h) ≠ 0 →
      ∃ x : p.adicCompletion ℚ, ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, h = unipotentGL2 x * k)
    (hbump1 : W₀ (iotaGL 1) = 1)
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hwlaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)), w (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g)
    (hwsm : ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g)
    (hθ : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ z : ℂˣ) : ℂ) * w g)
    (φ φ₁ : p.adicCompletion ℚ → ℂ) (hφ : IsSchwartzBruhat φ) (hφ₁ : IsSchwartzBruhat φ₁) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI := localBorel ℚ p

    (∀ t : (p.adicCompletion ℚ)ˣ, Valued.v (t : p.adicCompletion ℚ) = 1 → tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ (t : p.adicCompletion ℚ) = ((θ t : ℂˣ) : ℂ)) →
    (∀ y : p.adicCompletion ℚ, Valued.v y ≠ 1 → tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ y = 0) →
    (∀ t : (p.adicCompletion ℚ)ˣ, Valued.v (t : p.adicCompletion ℚ) = 1 → ∀ y : p.adicCompletion ℚ,
      tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ₁ ((t : p.adicCompletion ℚ) * y) = ((ω t : ℂˣ) : ℂ) * tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ₁ y) →
    (∀ y : p.adicCompletion ℚ, tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ₁ y ≠ 0 → Valued.v y ≤ WithZero.exp (-(f : ℤ))) →

    Measurable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          dualWhittakerFn3
            (fun X : LocalGL3 p => ∫ u : p.adicCompletion ℚ, ∫ y : p.adicCompletion ℚ,
              W₀ (X * longWeyl3 * upperUnipotent3 u 0 y) * (φ u * φ₁ y) ∂(selfDualHaarAt ℚ p) ∂(selfDualHaarAt ℚ p))
            (iotaGL g) *
          (((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
            w (w₀p * transposeInvN (Fin 2) g))) ∧

    (∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        dualWhittakerFn3
            (fun X : LocalGL3 p => ∫ u : p.adicCompletion ℚ, ∫ y : p.adicCompletion ℚ,
              W₀ (X * longWeyl3 * upperUnipotent3 u 0 y) * (φ u * φ₁ y) ∂(selfDualHaarAt ℚ p) ∂(selfDualHaarAt ℚ p))
            (iotaGL (unipotent x * g)) *
          (((modulus ((Matrix.GeneralLinearGroup.det (unipotent x * g) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
            w (w₀p * transposeInvN (Fin 2) (unipotent x * g))) =
        dualWhittakerFn3
            (fun X : LocalGL3 p => ∫ u : p.adicCompletion ℚ, ∫ y : p.adicCompletion ℚ,
              W₀ (X * longWeyl3 * upperUnipotent3 u 0 y) * (φ u * φ₁ y) ∂(selfDualHaarAt ℚ p) ∂(selfDualHaarAt ℚ p))
            (iotaGL g) *
          (((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
            w (w₀p * transposeInvN (Fin 2) g))) ∧

    (∀ g : GL (Fin 2) (p.adicCompletion ℚ),
        dualWhittakerFn3
            (fun X : LocalGL3 p => ∫ u : p.adicCompletion ℚ, ∫ y : p.adicCompletion ℚ,
              W₀ (X * longWeyl3 * upperUnipotent3 u 0 y) * (φ u * φ₁ y) ∂(selfDualHaarAt ℚ p) ∂(selfDualHaarAt ℚ p))
            (iotaGL g) *
          (((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
            w (w₀p * transposeInvN (Fin 2) g)) ≠ 0 →
        ∃ (x : p.adicCompletion ℚ) (u : GL (Fin 2) (p.adicCompletion ℚ)),
          u ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ ∧ g = unipotent x * u) ∧

    (∃ C : ℝ, ∀ g ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
        ‖dualWhittakerFn3
            (fun X : LocalGL3 p => ∫ u : p.adicCompletion ℚ, ∫ y : p.adicCompletion ℚ,
              W₀ (X * longWeyl3 * upperUnipotent3 u 0 y) * (φ u * φ₁ y) ∂(selfDualHaarAt ℚ p) ∂(selfDualHaarAt ℚ p))
            (iotaGL g) *
          (((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
            w (w₀p * transposeInvN (Fin 2) g))‖ ≤ C) ∧

    (∀ (y x : p.adicCompletion ℚ) (a d : (p.adicCompletion ℚ)ˣ),
        (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set (GL (Fin 2) (p.adicCompletion ℚ))).indicator
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          dualWhittakerFn3
            (fun X : LocalGL3 p => ∫ u : p.adicCompletion ℚ, ∫ y : p.adicCompletion ℚ,
              W₀ (X * longWeyl3 * upperUnipotent3 u 0 y) * (φ u * φ₁ y) ∂(selfDualHaarAt ℚ p) ∂(selfDualHaarAt ℚ p))
            (iotaGL g) *
          (((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
            w (w₀p * transposeInvN (Fin 2) g)))
          (unipotentGL2 y * diagUnits2 d a * lowerUnipotentGL2 x) =
        (if Valued.v y ≤ 1 then (1 : ℂ) else 0) *
          (if Valued.v (a : p.adicCompletion ℚ) = 1 ∧ Valued.v (d : p.adicCompletion ℚ) = 1 then
            ((ω (a * d⁻¹) : ℂˣ) : ℂ) * tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ₁ x *
              w (w₀p * diagUnitGL2 (a * d⁻¹) * unipotent (-x))
          else 0)) := by sorry
