-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_integral_principalSeries2_mul_whittaker_iotaGL_diagUnits2_longWeyl3_eq_mul_of_forall_integral_localZeta31_eq_of_torusShell
-- name    : LanglandsTunnell.RankinSelberg.integral_principalSeries2_mul_whittaker_iotaGL_diagUnits2_longWeyl3_eq_mul_of_forall_integral_localZeta31_eq_of_torusShell
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/1fd87684-e385-5ac3-a864-19f80e2d55f7
-- title:
--   Primal transport of the local GL₃timesGL₁ functional equation
-- statement:
--   Fix a nonzero prime $p$ of $\mathbb{Z}$, write $F=\mathbb{Q}_p$ for the completion, $q=\#(\mathbb{Z}/p)$ for the absolute norm of $p$, $\psi$ for the standard local additive character `psiLocal` at $p$, $\nu$ for the self-dual additive Haar measure `selfDualHaarAt`, and $d^{\times}$ for the multiplicative measure obtained by pulling back $|x|^{-1}\,d\nu(x)$ along $F^{\times}\hookrightarrow F$; $|\cdot|$ denotes `modulus`, which on $F$ is the norm. Let $\varpi$ lie in the valuation ring with nonzero image and $v(\varpi)=\exp(-1)$. Let $V:\mathrm{GL}_3(F)\to\mathbb{C}$ satisfy $V(n(x,y,z)g)=\psi^{-1}(x+y)V(g)$ for the upper unipotent $n(x,y,z)$, be invariant under right translation by some open subgroup, and have central character $\omega$, i.e. $V(z\cdot 1_3\,g)=\omega(z)V(g)$. Let $\chi_0,\chi_1$ be characters $F^{\times}\to\mathbb{C}^{\times}$, $C_1\in\mathbb{C}$, $k_1\in\mathbb{Z}$. Assume (torus finiteness) for each $h\in\mathrm{GL}_2(F)$ there is a finite set $T\subset\mathbb{Z}$ with $\int_{|u|=1}V(\iota(\mathrm{diag}(\varpi^{n}u,1)h))\chi_1(u)\,d^{\times}u=0$ for all $n\notin T$, where $\iota(h)=\mathrm{diag}(h,1)$; and (functional equations) for every $V'$ in the span of the right translates of $V$ and every $g\in\mathrm{GL}_3(F)$ there are polynomials $Q_1,Q_2$ with $Q_2\neq0$, an integer $n$ and reals $\sigma_0,\sigma_1$ such that the integrand of $Z_0(s;V',\chi_1;g)=\int V'(\iota(\mathrm{diag}(a,1))g)\chi_1(a)|a|^{s-1}d^{\times}a$ is integrable for $\mathrm{Re}\,s>\sigma_0$ with $Z_0(s;V',\chi_1;g)\,Q_2(q^{-s})=Q_1(q^{-s})q^{ns}$ there, the integrand of the dual integral $Z_1(1-s;\widetilde{V'},\chi_1^{-1};w'\,{}^{t}g^{-1})$ (with $\widetilde W(h)=W(w_3\,{}^{t}h^{-1})$, $w_3$ the long Weyl element and $w'$ the transposition of the last two coordinates) is integrable for $\mathrm{Re}\,(1-s)>\sigma_1$, and there $Z_1(1-s;\widetilde{V'},\chi_1^{-1};w'\,{}^{t}g^{-1})\,Q_2(q^{-s})=Q_1(q^{-s})q^{ns}\,(C_1q^{k_1s})$. Let $f$ lie in the principal series attached to $(\chi_0,\chi_1)$, namely $f$ locally constant, invariant under left translation by upper unipotents and satisfying $f(\mathrm{diag}(a_0,a_1)g)=\chi_0(a_0)\chi_1(a_1)\sqrt{|a_0|/|a_1|}\,f(g)$; let $w_0$ be the antidiagonal permutation in $\mathrm{GL}_2(F)$, let $P$ be a polynomial, $m\in\mathbb{Z}$ and $\sigma_a,\sigma_b\in\mathbb{R}$. Then for every Haar measure $\mu_2$ on $\mathrm{GL}_2(F)$, given (L1) some $\sigma_P$ with $g\mapsto V(\iota g)f(w_0g)|\det g|^{s-1/2}$ $\mu_2$-integrable for $\mathrm{Re}\,s>\sigma_P$, (L2) some $\sigma_I$ such that for $\mathrm{Re}\,s>\sigma_I$ one has $\int_F f(w_0u(y))\bigl(\int_{F^{\times}}\chi_0(a)|a|^{s-1}Z_1(s;V,\chi_1;\iota(\mathrm{diag}(1,a)u(y)))\,d^{\times}a\bigr)d\nu(y)=q^{ms}P(q^{-s})$, and (L3) integrability, for $\sigma_a<\mathrm{Re}\,s<\sigma_b$, of $(y,t,a)\mapsto f(w_0u(y))\,\chi_1(t)^{-1}\omega(t)^{-1}|t|^{s}\chi_0(a)|a|^{-s-1}V(\iota(\mathrm{diag}(at,t))\,w_3\,n(0,0,y)\,w')$ against $\nu\otimes d^{\times}\otimes d^{\times}$, it follows that for all $s$ with $\sigma_a<\mathrm{Re}\,s<\sigma_b$ the integral of that function equals $\bigl(C_1q^{-k_1s}\bigr)\bigl(q^{-ms}P(q^{s})\bigr)$.
--
--   This is the primal half of the transport step in the local multiplicativity of the $\mathrm{GL}_3\times\mathrm{GL}_2$ gamma factor when the $\mathrm{GL}_2$ partner is a principal series: the assumed $\mathrm{GL}_3\times\mathrm{GL}_1$ functional equations for the whole cyclic span of $V$, together with the evaluation (L2) of the unfolded middle integral as $q^{ms}P(q^{-s})$, force the corresponding integral over $F\times F^{\times}\times F^{\times}$ at $-s$ to be $C_1q^{-k_1s}$ times $q^{-ms}P(q^{s})$. It feeds the statement producing the functional equation of the local Rankin–Selberg integral against the Jacquet–Whittaker function of $f$ and its dual.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_integral_principalSeries2_mul_whittaker_iotaGL_diagUnits2_longWeyl3_eq_mul_of_forall_integral_localZeta31_eq_of_torusShell.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SmoothingKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal
  LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.RankinSelberg.integral_principalSeries2_mul_whittaker_iotaGL_diagUnits2_longWeyl3_eq_mul_of_forall_integral_localZeta31_eq_of_torusShell
    (p : HeightOneSpectrum (𝓞 ℚ))
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))

    (V : LocalGL3 p → ℂ) (hVlaw : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ V)
    (hVsm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, V (g * k) = V g)
    (ω : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hVω : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : LocalGL3 p),
      V (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((ω z : ℂˣ) : ℂ) * V g)
    (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (C₁ : ℂ) (k₁ : ℤ)

    (hT : letI := localBorel ℚ p
      ∀ h : GL (Fin 2) (p.adicCompletion ℚ), ∃ T : Finset ℤ, ∀ n : ℤ, n ∉ T →
        ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
          V (iotaGL (diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ
            ^ n * u) * h)) * ((χ 1 u : ℂˣ) : ℂ) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) = 0)

    (h31 : ∀ V' ∈ gl3CyclicSubspace V, ∀ g : LocalGL3 p,
      letI := localBorel ℚ p
      ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
        IsLocalZeta30ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) V' (χ 1) g σ₀ ∧
        (∀ s : ℂ, σ₀ < s.re →
          localZeta30 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) V' (χ 1) s g *
            Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
          Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
        IsLocalZeta31ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
          (selfDualHaarAt ℚ p) (dualWhittakerFn3 V') ((χ 1))⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
        (∀ s : ℂ, σ₁ < (1 - s).re →
          localZetaDual31 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p)
            V' (χ 1) (1 - s) g * Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
          Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s) *
            (C₁ * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k₁ : ℂ) * s))))

    (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hf : f ∈ principalSeries2 p χ)
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (P : Polynomial ℂ) (m : ℤ) (σa σb : ℝ) :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],

      (∃ σP : ℝ, ∀ s : ℂ, σP < s.re →
        Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          (V (iotaGL g) * f (w₀p * g)) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^
              (s - 1 / 2)) μ₂) →

      (∃ σI : ℝ, ∀ s : ℂ, σI < s.re →
        ∫ y, f (w₀p * unipotentGL2 y) *
          (∫ a, ((χ 0 a : ℂˣ) : ℂ) * ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) *
            localZeta31 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p)
              V (χ 1) s (iotaGL (diagUnits2 1 a * unipotentGL2 y))
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∂(selfDualHaarAt ℚ p) =
        (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) →

      (∀ s : ℂ, σa < s.re → s.re < σb →
        Integrable (fun yat : p.adicCompletion ℚ × ((p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ) =>
          f (w₀p * upperUnipotent2 p yat.1) *
            (((((χ 1) yat.2.1 : ℂˣ) : ℂ)⁻¹ * ((ω yat.2.1 : ℂˣ) : ℂ)⁻¹ *
                ((modulus (yat.2.1 : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s *
              ((((χ 0) yat.2.2 : ℂˣ) : ℂ) * ((modulus (yat.2.2 : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-s - 1))) *
            V (iotaGL (diagUnits2 (yat.2.2 * yat.2.1) yat.2.1) *
              (longWeyl3 * upperUnipotent3 0 0 yat.1 * weylPrime3))))
          ((selfDualHaarAt ℚ p).prod
            ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod
              (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))))) →
      ∀ s : ℂ, σa < s.re → s.re < σb →
        (∫ yat : p.adicCompletion ℚ × ((p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ),
          f (w₀p * upperUnipotent2 p yat.1) *
            (((((χ 1) yat.2.1 : ℂˣ) : ℂ)⁻¹ * ((ω yat.2.1 : ℂˣ) : ℂ)⁻¹ *
                ((modulus (yat.2.1 : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s *
              ((((χ 0) yat.2.2 : ℂˣ) : ℂ) * ((modulus (yat.2.2 : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-s - 1))) *
            V (iotaGL (diagUnits2 (yat.2.2 * yat.2.1) yat.2.1) *
              (longWeyl3 * upperUnipotent3 0 0 yat.1 * weylPrime3)))
          ∂((selfDualHaarAt ℚ p).prod
            ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod
              (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))))) =
        (C₁ * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k₁ : ℂ) * (-s))) *
          ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s)) := by sorry
