-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_godementZeta2_boxIndicator_eq_mul_torusZeta_of_isOpen_of_chart
-- name    : LanglandsTunnell.RankinSelberg.godementZeta2_boxIndicator_eq_mul_torusZeta_of_isOpen_of_chart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/2032db9f-7b77-5121-8c7e-7bb4024d1121
-- title:
--   Godement zeta on a box as constant times torus zeta
-- statement:
--   Fix a nonzero prime $p$ of $\mathcal O_{\mathbb Q}$, write $F=\mathbb Q_p$ for the completion, and let $|\cdot|=\mathrm{modulus}$ be the module of $F$ (the Haar scaling factor of multiplication, and $0$ at $0$), $dx=\mathtt{selfDualHaarAt}$ the additive Haar measure normalised by $(\mathrm{absNorm}\,p)^{-n/2}$ where $n$ is the level of the standard character $\psi=\mathtt{psiLocal}$, and $d^\times y$ the multiplicative Haar measure on $F^\times$ obtained by pulling back $|x|^{-1}dx$ on $F\setminus\{0\}$ along $F^\times\hookrightarrow F$. Let $w:GL_2(F)\to\mathbb C$ satisfy $w(n(x)g)=\psi(x)w(g)$ for all $x,g$, where $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$; let $\chi:F^\times\to\mathbb C^\times$ be a locally constant homomorphism; let $U\le GL_2(F)$ be an open subgroup with $w(gk)=w(g)$ for $k\in U$; and let $L,M_b,M_c\ge 0$, $M_d\ge 1$ be integers such that $w(\mathrm{diag}(y,1))=0$ whenever $v(y)>\exp L$, such that $\mathrm{diag}(1,a)\,n^-(y)\in U$ whenever $v(a-1)\le\exp(-M_d)$ and $v(y)\le\exp(-M_c)$ (here $n^-(y)=\begin{pmatrix}1&0\\y&1\end{pmatrix}$), and such that $\chi(a)=1$ whenever $v(a-1)\le\exp(-M_d)$. Let $\Phi_0$ be the $\mathbb C$-valued indicator of the box $\{X: v(X_{00})\le\exp L,\ v(X_{01})\le\exp(-M_b),\ v(X_{10})\le\exp(-M_c),\ v(X_{11}-1)\le\exp(-M_d)\}$ in $M_2(F)$. The assertion is: for every Haar measure $\mu_2$ on $GL_2(F)$ (with the Borel structure coming from the topology) and every $c\in[0,\infty]$ with $c\ne 0,\infty$ such that $\mu_2$ is $c$ times the image of $dx\,d^\times a\,d^\times b\,dy$ weighted by the density $|a b^{-1}|$ under the Bruhat chart $(x,a,b,y)\mapsto n(x)\,\mathrm{diag}(b,a)\,n^-(y)$, the constant $$C=c\cdot \mathrm{vol}\{v(x)\le\exp(-M_b)\}\cdot \mathrm{vol}^\times\{v(a-1)\le\exp(-M_d)\}\cdot \mathrm{vol}\{v(x)\le\exp(-M_c)\}$$ (real parts of these measures, cast to $\mathbb C$) is nonzero, and for each $s\in\mathbb C$ for which $y\mapsto w(\mathrm{diag}(y,1))\chi(y)|y|^{s-1/2}$ is $d^\times y$-integrable, the function $g\mapsto w(g)\Phi_0(g)\chi(\det g)|\det g|^{s+1/2}$ is $\mu_2$-integrable and $\mathtt{godementZeta2}$ at $s+\tfrac12$, namely $\int_{GL_2(F)} w(g)\Phi_0(g)\chi(\det g)|\det g|^{s+1/2}\,d\mu_2$, equals $C\int_{F^\times} w(\mathrm{diag}(y,1))\chi(y)|y|^{s-1/2}\,d^\times y$.
--
--   This is the local computation, in the style of Godement's method as used by Jacquet and Langlands, which evaluates a Godement–Jacquet zeta integral on $GL_2(F)$ for a test function concentrated on a small box around the diagonal, reducing it to the Tate-type zeta integral of the restriction of the Whittaker function to the diagonal torus, with an explicit nonzero volume constant. It is the primal half of [`LanglandsTunnell.RankinSelberg.exists_schwartz_godementZeta2_whittaker_eq_mul_torusZeta_and_dual_of_integrable`](thm.html#LanglandsTunnell.RankinSelberg.exists_schwartz_godementZeta2_whittaker_eq_mul_torusZeta_and_dual_of_integrable), whose dual half carries the same constant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_godementZeta2_boxIndicator_eq_mul_torusZeta_of_isOpen_of_chart.lean

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

theorem LanglandsTunnell.RankinSelberg.godementZeta2_boxIndicator_eq_mul_torusZeta_of_isOpen_of_chart
    (p : HeightOneSpectrum (𝓞 ℚ))
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hwlaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g)
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχc : IsLocallyConstant χ)
    (U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) (hUo : IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))))
    (hU : ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g)
    (L Mb Mc Md : ℤ) (hL : 0 ≤ L) (hMb : 0 ≤ Mb) (hMc : 0 ≤ Mc) (hMd : 1 ≤ Md)
    (hsupp : ∀ y : (p.adicCompletion ℚ)ˣ, WithZero.exp L < Valued.v (y : p.adicCompletion ℚ) → w (diagOne y) = 0)
    (hstab : ∀ (a : (p.adicCompletion ℚ)ˣ) (y : p.adicCompletion ℚ),
      Valued.v ((a : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-Md) → Valued.v y ≤ WithZero.exp (-Mc) →
        diagUnits2 1 a * lowerUnipotentGL2 y ∈ U)
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
      (((c.toReal : ℝ) : ℂ) *
            (((selfDualHaarAt ℚ p) {x : p.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (-Mb)}).toReal : ℂ) *
            (((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) {a : (p.adicCompletion ℚ)ˣ | Valued.v ((a : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-Md)}).toReal : ℂ) *
            (((selfDualHaarAt ℚ p) {x : p.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (-Mc)}).toReal : ℂ)) ≠ 0 ∧
      ∀ s : ℂ,
        Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
          w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) →
        Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          w g * Φ₀ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2)) μ₂ ∧
        godementZeta2 p μ₂ w Φ₀ χ (s + 1 / 2) =
          (((c.toReal : ℝ) : ℂ) *
            (((selfDualHaarAt ℚ p) {x : p.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (-Mb)}).toReal : ℂ) *
            (((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) {a : (p.adicCompletion ℚ)ˣ | Valued.v ((a : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-Md)}).toReal : ℂ) *
            (((selfDualHaarAt ℚ p) {x : p.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (-Mc)}).toReal : ℂ)) *
            ∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) := by sorry
