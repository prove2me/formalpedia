-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_mul_integral_transposeInvN_mul_whittaker_iotaGL_diagUnits2_longWeyl3_eq_of_forall_integral_localZeta31_dualWhittakerFn3_eq_of_torusShell
-- name    : LanglandsTunnell.RankinSelberg.mul_integral_transposeInvN_mul_whittaker_iotaGL_diagUnits2_longWeyl3_eq_of_forall_integral_localZeta31_dualWhittakerFn3_eq_of_torusShell
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/a752014f-ef5e-524a-ba51-aafbf35a0d64
-- title:
--   Dual transport of the GL₃timesGL₁ functional equation
-- statement:
--   Fix a finite place $p$ of $\mathbb{Q}$, write $F = \mathbb{Q}_p$ for the completion, $q = \#(\mathcal{O}_{\mathbb{Q}}/p)$, $\nu$ for the self-dual additive Haar measure `selfDualHaarAt ℚ p` on $F$ and $d^\times$ for the measure on $F^\times$ obtained by pulling back $|x|^{-1}\,d\nu$ along $F^\times\hookrightarrow F$, and $|\cdot| =$ `modulus`. Let $\varpi$ be an element of the valuation ring with nonzero image in $F$ and valuation $\exp(-1)$. Let $V:\mathrm{GL}_3(F)\to\mathbb{C}$ satisfy $V(n(x,y,z)g) = \psi^{-1}(x+y)V(g)$ for the standard local additive character $\psi =$ `psiLocal ℚ p` and all upper unipotent $n(x,y,z)$, be right invariant under some open subgroup, and have central character $\omega$, so $V(z\cdot g) = \omega(z)V(g)$ for scalar $z$. Let $\chi_0,\chi_1$ be quasi-characters of $F^\times$, $C_0\in\mathbb{C}$, $k_0\in\mathbb{Z}$. Assume (hT) for each $h\in\mathrm{GL}_2(F)$ the integrals $\int_{|u|=1}\widetilde V(\iota(\mathrm{diag}(\varpi^n u,1)h))\chi_0(u)^{-1}\,d^\times u$ vanish for all $n$ outside a finite set, where $\widetilde V(g) = V(w_3\,{}^tg^{-1})$ and $\iota(h) = \mathrm{diag}(h,1)$; and (h31) for every $V'$ in the span of the right translates of $V$ and every $g\in\mathrm{GL}_3(F)$ there are polynomials $Q_1,Q_2$ with $Q_2\neq 0$, an integer $n$ and reals $\sigma_0,\sigma_1$ such that the integrand of `localZeta30` $(V',\chi_0;g)$ is integrable and $Z_0(s)Q_2(q^{-s}) = Q_1(q^{-s})q^{ns}$ for $\mathrm{Re}\,s>\sigma_0$, while the integrand defining `localZeta31` for $\widetilde{V'}$, $\chi_0^{-1}$ at $w'\,{}^tg^{-1}$ is jointly integrable above $\sigma_1$ and `localZetaDual31`$(V',\chi_0;1-s,g)\,Q_2(q^{-s}) = Q_1(q^{-s})q^{ns}\,C_0q^{k_0 s}$ whenever $\sigma_1 < \mathrm{Re}(1-s)$. Let $\chi_0^D(a) = \chi_1(a)^{-1}|a|$, $\chi_1^D(a) = \chi_0(a)^{-1}|a|$, let $f:\mathrm{GL}_2(F)\to\mathbb{C}$ and $w_0 = \begin{pmatrix}0&1\\1&0\end{pmatrix}$ be such that $h\mapsto |\det h|\,f(w_0\,{}^th^{-1})$ lies in the principal series `principalSeries2 p` $\chi^D$ (locally constant, invariant under left multiplication by upper unipotents, and transforming by $\chi^D(a)\,\delta^{1/2}(a)$ under left multiplication by diagonal $a$), and let $P_d$ be a polynomial, $m_d\in\mathbb{Z}$ and $\sigma_a,\sigma_b$ reals. Then, for every Haar measure $\mu_2$ on $\mathrm{GL}_2(F)$, assuming (A) there is $\sigma_D$ with $g\mapsto \widetilde V(\iota(g))\,|\det(w_0g)|\,f(w_0\,{}^t(w_0g)^{-1})\,|\det g|^{s-1/2}$ $\mu_2$-integrable for $\mathrm{Re}\,s>\sigma_D$; (B) there is $\sigma_I$ such that for $\mathrm{Re}\,s>\sigma_I$ the iterated integral over $y\in F$ of $|\det(w_0u(y))|f(w_0\,{}^t(w_0u(y))^{-1})$ times $\int \chi^D_0(a)|a|^{s-1}\,$`localZeta31`$(\widetilde V,\chi^D_1;s,\iota(\mathrm{diag}(1,a)u(y)))\,d^\times a$ equals $q^{m_ds}P_d(q^{-s})$, with $u(y)$ the upper unipotent with entry $y$; and (C) for $\sigma_a<\mathrm{Re}\,s<\sigma_b$ the function $$(y,a,t)\mapsto f(w_0\,{}^t(w_0u(y))^{-1})\,\chi_1(a)^{-1}\omega(a)^{-1}|a|^{s}\,\chi_0(t)|t|^{-s-1}\,V(\iota(\mathrm{diag}(ta,a))\,w_3\,n(0,0,-y)\,w_3\,w')$$ is integrable for $\nu\otimes d^\times\otimes d^\times$ — it follows that for all $s$ with $\sigma_a<\mathrm{Re}\,s<\sigma_b$ one has $C_0q^{-k_0s}$ times the triple integral in (C) equal to $q^{m_ds}P_d(q^{-s})$.
--
--   This is the dual half of the transport step in the proof of multiplicativity of the local $\mathrm{GL}_3\times\mathrm{GL}_2$ gamma factor in the $\mathrm{GL}_2$ variable when the $\mathrm{GL}_2$ partner is a principal series: the $\chi_0$-twisted $\mathrm{GL}_3\times\mathrm{GL}_1$ functional equation (h31) is carried through the unfolded dual double integral, so that $C_0q^{-k_0s}$ times the dual middle integral is the Laurent-polynomial expression $q^{m_ds}P_d(q^{-s})$ coming from the dual principal-series side. It feeds the comparison of the Rankin–Selberg local integral with its dual, `exists_rsLocalIntegral_jacquetIntegral_dual_eq_mul_of_forall_localZeta31_fe_of_integrable_setIntegral_localLevelOne_of_torusShell`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_mul_integral_transposeInvN_mul_whittaker_iotaGL_diagUnits2_longWeyl3_eq_of_forall_integral_localZeta31_dualWhittakerFn3_eq_of_torusShell.lean

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

theorem LanglandsTunnell.RankinSelberg.mul_integral_transposeInvN_mul_whittaker_iotaGL_diagUnits2_longWeyl3_eq_of_forall_integral_localZeta31_dualWhittakerFn3_eq_of_torusShell
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
    (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (C₀ : ℂ) (k₀ : ℤ)

    (hT : letI := localBorel ℚ p
      ∀ h : GL (Fin 2) (p.adicCompletion ℚ), ∃ T : Finset ℤ, ∀ n : ℤ, n ∉ T →
        ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
          dualWhittakerFn3 V (iotaGL (diagUnitGL2
            (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n * u) * h)) *
            ((χ 0 u : ℂˣ) : ℂ)⁻¹ ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) = 0)

    (h31 : ∀ V' ∈ gl3CyclicSubspace V, ∀ g : LocalGL3 p,
      letI := localBorel ℚ p
      ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
        IsLocalZeta30ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) V' (χ 0) g σ₀ ∧
        (∀ s : ℂ, σ₀ < s.re →
          localZeta30 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) V' (χ 0) s g *
            Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
          Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
        IsLocalZeta31ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
          (selfDualHaarAt ℚ p) (dualWhittakerFn3 V') ((χ 0))⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
        (∀ s : ℂ, σ₁ < (1 - s).re →
          localZetaDual31 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p)
            V' (χ 0) (1 - s) g * Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
          Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s) *
            (C₀ * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k₀ : ℂ) * s))))

    (χD : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (hχD0 : ∀ a : (p.adicCompletion ℚ)ˣ,
      ((χD 0 a : ℂˣ) : ℂ) = ((χ 1 a : ℂˣ) : ℂ)⁻¹ * (((modulus (a : p.adicCompletion ℚ) : ℝ)) : ℂ))
    (hχD1 : ∀ a : (p.adicCompletion ℚ)ˣ,
      ((χD 1 a : ℂˣ) : ℂ) = ((χ 0 a : ℂˣ) : ℂ)⁻¹ * (((modulus (a : p.adicCompletion ℚ) : ℝ)) : ℂ))
    (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (hfD : (fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
        (((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ)) : ℂ) *
          f (w₀p * AutomorphicForm.transposeInvN (Fin 2) h)) ∈ principalSeries2 p χD)
    (Pd : Polynomial ℂ) (md : ℤ) (σa σb : ℝ) :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],

      (∃ σD : ℝ, ∀ s : ℂ, σD < s.re →
        Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          (dualWhittakerFn3 V (iotaGL g) *
              (((modulus ((Matrix.GeneralLinearGroup.det (w₀p * g) : (p.adicCompletion ℚ)ˣ) :
                  p.adicCompletion ℚ) : ℝ) : ℂ) *
                f (w₀p * AutomorphicForm.transposeInvN (Fin 2) (w₀p * g)))) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^
              (s - 1 / 2)) μ₂) →

      (∃ σI : ℝ, ∀ s : ℂ, σI < s.re →
        ∫ y, (((modulus ((Matrix.GeneralLinearGroup.det (w₀p * unipotentGL2 y) : (p.adicCompletion ℚ)ˣ) :
                p.adicCompletion ℚ) : ℝ) : ℂ) *
              f (w₀p * AutomorphicForm.transposeInvN (Fin 2) (w₀p * unipotentGL2 y))) *
          (∫ a, ((χD 0 a : ℂˣ) : ℂ) * ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) *
            localZeta31 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p)
              (dualWhittakerFn3 V) (χD 1) s (iotaGL (diagUnits2 1 a * unipotentGL2 y))
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∂(selfDualHaarAt ℚ p) =
        (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) →

      (∀ s : ℂ, σa < s.re → s.re < σb →
        Integrable (fun yat : p.adicCompletion ℚ × ((p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ) =>
          f (w₀p * AutomorphicForm.transposeInvN (Fin 2) (w₀p * upperUnipotent2 p yat.1)) *
            (((((χ 1) yat.2.1 : ℂˣ) : ℂ)⁻¹ * ((ω yat.2.1 : ℂˣ) : ℂ)⁻¹ *
                ((modulus (yat.2.1 : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s *
              ((((χ 0) yat.2.2 : ℂˣ) : ℂ) * ((modulus (yat.2.2 : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-s - 1))) *
            V (iotaGL (diagUnits2 (yat.2.2 * yat.2.1) yat.2.1) *
              (longWeyl3 * upperUnipotent3 0 0 (-yat.1) * longWeyl3 * weylPrime3))))
          ((selfDualHaarAt ℚ p).prod
            ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod
              (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))))) →
      ∀ s : ℂ, σa < s.re → s.re < σb →
        (C₀ * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k₀ : ℂ) * (-s))) *
          (∫ yat : p.adicCompletion ℚ × ((p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ),
            f (w₀p * AutomorphicForm.transposeInvN (Fin 2) (w₀p * upperUnipotent2 p yat.1)) *
              (((((χ 1) yat.2.1 : ℂˣ) : ℂ)⁻¹ * ((ω yat.2.1 : ℂˣ) : ℂ)⁻¹ *
                  ((modulus (yat.2.1 : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s *
                ((((χ 0) yat.2.2 : ℂˣ) : ℂ) * ((modulus (yat.2.2 : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-s - 1))) *
              V (iotaGL (diagUnits2 (yat.2.2 * yat.2.1) yat.2.1) *
                (longWeyl3 * upperUnipotent3 0 0 (-yat.1) * longWeyl3 * weylPrime3)))
            ∂((selfDualHaarAt ℚ p).prod
              ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod
                (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))))) =
        (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) := by sorry
