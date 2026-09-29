-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_godementZeta2_transposeInv_matFourier22_boxIndicator_eq_mul_torusZeta_dual_of_integrable_of_chart
-- name    : LanglandsTunnell.RankinSelberg.godementZeta2_transposeInv_matFourier22_boxIndicator_eq_mul_torusZeta_dual_of_integrable_of_chart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/2240bffa-1c11-5f5b-aa4a-2baa63e8d5f3
-- title:
--   Dual Godement–Jacquet zeta of the Fourier-transformed torus box
-- statement:
--   Let $p$ be a prime of $\mathcal O_{\mathbb Q}$, write $F=\mathbb Q_p$ for `p.adicCompletion ℚ` and $\psi$ for `psiLocal ℚ p`. Let $w:GL_2(F)\to\mathbb C$ satisfy $w(n(x)g)=\psi(x)w(g)$ for all $x\in F$, $g$, and $w(zg)=\theta_0(z)w(g)$ for a character $\theta_0:F^\times\to\mathbb C^\times$ and scalar matrices $z$; let $\chi:F^\times\to\mathbb C^\times$ be locally constant, $U\le GL_2(F)$ open with $w(gk)=w(g)$ for $k\in U$, and $w_J$ the unit with matrix $!![0,1;-1,0]$. Fix integers $L,M_b,M_c,M_d$ with $M_d\le L$, $M_b,M_c\ge 0$, $M_d\ge 1$, such that $w(\mathrm{diag}(y,1)w_J)=0$ whenever $v(y)>\exp M_c$; $n(x)\in U$ for $v(x)\le\exp(-L)$; $\mathrm{diag}(a,1)\in U$, $\theta_0(a)=1$ and $\chi(a)=1$ for $v(a-1)\le\exp(-M_d)$. Let $\Phi_0$ be the indicator of $\{v(X_{00})\le\exp L,\ v(X_{01})\le\exp(-M_b),\ v(X_{10})\le\exp(-M_c),\ v(X_{11}-1)\le\exp(-M_d)\}$. Then for every Haar measure $\mu_2$ on $GL_2(F)$ (Borel structure `localGLBorel`) and every $c\in[0,\infty]$ with $c\ne 0,\infty$ such that $\mu_2$ is $c$ times the image, under $(x,a,b,y)\mapsto n(x)\,\mathrm{diag}(b,a)\,n^-(y)$, of the product of the self-dual additive Haar measure on $F$, the measures `Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))` on the two copies of $F^\times$ and the self-dual measure on $F$, weighted by the density $|ab^{-1}|$ (here $|\cdot|$ is `modulus`, the module of the distributive Haar character), and for every $s\in\mathbb C$: if $g\mapsto w({}^t g^{-1})\,\widehat{\Phi_0}(g)\,\chi^{-1}(\det g)\,|\det g|^{s+3/2}$ is $\mu_2$-integrable, where $\widehat{\Phi_0}=$ `matFourier22 p ψ Φ₀` is the iterated column-wise Fourier transform of $\Phi_0$ (first in column $1$, then in column $0$, each against $\psi(u_1X_{0j}+u_2X_{1j})$ over the self-dual square measure), then $y\mapsto w(\mathrm{diag}(y,1)w_J)\,\chi(y)^{-1}\theta_0(y)^{-1}|y|^{1/2+s}$ is integrable for the multiplicative measure, and `godementZeta2 p μ₂` of $g\mapsto w({}^tg^{-1})$, $\widehat{\Phi_0}$, $\chi^{-1}$ at $s+3/2$ equals $c\cdot\mathrm{vol}\{v(x)\le\exp(-M_b)\}\cdot\mathrm{vol}^\times\{v(a-1)\le\exp(-M_d)\}\cdot\mathrm{vol}\{v(x)\le\exp(-M_c)\}$ (real values, coerced to $\mathbb C$) times that torus integral.
--
--   This is the dual half of the test-function comparison in the Godement–Jacquet treatment of $GL_2$: the zeta integral of the Whittaker function $g\mapsto w({}^tg^{-1})$ against the Fourier transform of an explicit box indicator is evaluated as an explicit constant times the Tate-type zeta integral of the Kirillov function $y\mapsto w(\mathrm{diag}(y,1)w_J)$ at $1/2+s$. Together with the corresponding primal identity, in which the same constant occurs, it feeds the construction of a Schwartz test function linking the Godement–Jacquet and torus zeta integrals used by [`LanglandsTunnell.RankinSelberg.exists_schwartz_godementZeta2_whittaker_eq_mul_torusZeta_and_dual_of_integrable`](thm.html#LanglandsTunnell.RankinSelberg.exists_schwartz_godementZeta2_whittaker_eq_mul_torusZeta_and_dual_of_integrable).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_godementZeta2_transposeInv_matFourier22_boxIndicator_eq_mul_torusZeta_dual_of_integrable_of_chart.lean

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
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

theorem LanglandsTunnell.RankinSelberg.godementZeta2_transposeInv_matFourier22_boxIndicator_eq_mul_torusZeta_dual_of_integrable_of_chart
    (p : HeightOneSpectrum (𝓞 ℚ))
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hwlaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g)
    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w g)
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχc : IsLocallyConstant χ)
    (U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) (hUo : IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))))
    (hU : ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g)
    (wJ : GL (Fin 2) (p.adicCompletion ℚ)) (hwJ : (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; -1, 0])
    (L Mb Mc Md : ℤ) (hL : Md ≤ L) (hMb : 0 ≤ Mb) (hMc : 0 ≤ Mc) (hMd : 1 ≤ Md)
    (hsuppJ : ∀ y : (p.adicCompletion ℚ)ˣ, WithZero.exp Mc < Valued.v (y : p.adicCompletion ℚ) → w (diagOne y * wJ) = 0)
    (hstabN : ∀ x : p.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-L) → unipotent x ∈ U)
    (hstabD : ∀ a : (p.adicCompletion ℚ)ˣ, Valued.v ((a : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-Md) → diagOne a ∈ U)
    (hθ₀ : ∀ a : (p.adicCompletion ℚ)ˣ, Valued.v ((a : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-Md) → θ₀ a = 1)
    (hχ : ∀ a : (p.adicCompletion ℚ)ˣ, Valued.v ((a : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-Md) → χ a = 1)
    (Φ₀ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hΦ₀ : Φ₀ = fun X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) =>
        Set.indicator {X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) |
            Valued.v (X 0 0) ≤ WithZero.exp L ∧ Valued.v (X 0 1) ≤ WithZero.exp (-Mb) ∧
            Valued.v (X 1 0) ≤ WithZero.exp (-Mc) ∧ Valued.v (X 1 1 - 1) ≤ WithZero.exp (-Md)} (fun _ => (1 : ℂ)) X) :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure] (c : ENNReal), c ≠ 0 → c ≠ ⊤ →
      μ₂ = c • Measure.map
          (fun q : (p.adicCompletion ℚ) × (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ) =>
            unipotentGL2 q.1 * diagUnits2 q.2.2.1 q.2.1 * lowerUnipotentGL2 q.2.2.2)
          ((((selfDualHaarAt ℚ p).prod ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod (selfDualHaarAt ℚ p))))).withDensity fun q =>
            (modulus (((q.2.1 * (q.2.2.1)⁻¹ : (p.adicCompletion ℚ)ˣ)) : p.adicCompletion ℚ) : ENNReal)) →
      ∀ s : ℂ,
        Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          w (transposeInvN (Fin 2) g) *
            matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ₀ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
            ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 3 / 2)) μ₂ →
        Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
          w (diagOne y * wJ) * (((χ y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
            ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 + s)) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
        godementZeta2 p μ₂ (fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (transposeInvN (Fin 2) g))
            (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ₀) χ⁻¹ (s + 3 / 2) =
          (((c.toReal : ℝ) : ℂ) *
            (((selfDualHaarAt ℚ p) {x : p.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (-Mb)}).toReal : ℂ) *
            (((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) {a : (p.adicCompletion ℚ)ˣ | Valued.v ((a : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-Md)}).toReal : ℂ) *
            (((selfDualHaarAt ℚ p) {x : p.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (-Mc)}).toReal : ℂ)) *
            ∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y * wJ) * (((χ y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 + s) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) := by sorry
