-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_and_godementZeta2_transposeInv_matFourier22_eq_mul_twoVarZeta_fourierSlice_of_mem_principalSeries2
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_integrable_and_godementZeta2_transposeInv_matFourier22_eq_mul_twoVarZeta_fourierSlice_of_mem_principalSeries2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/df8d542b-fa5f-57e5-ac68-8bb96fd31f14
-- title:
--   Godement unfolding of the contragredient local GL₂ zeta integral
-- statement:
--   Fix a height-one prime $p$ of $\mathcal O_{\mathbb Q}$, write $F_p =$ `p.adicCompletion ℚ` with its Borel $\sigma$-algebra (and the Borel structure on $GL_2(F_p)$), let $\mathrm{lam} : \mathrm{Fin}\,2 \to (F_p^\times \to \mathbb C^\times)$ be two locally constant characters and $\chi$ a further locally constant character of $F_p^\times$. Let $\mu_2$ be a Haar measure on $GL_2(F_p)$ and $\kappa>0$ a constant for which the Iwasawa integration formula holds in the following form: for every measurable $G : GL_2(F_p)\to[0,\infty]$, $\int^- G\,d\mu_2$ equals $\kappa$ times the integral, over the product of $\mu_2$ restricted to the subgroup [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤`](def/AdelicDock_LocalEmbedding.html#L178) (the pullback along the local embedding at $p$ of the finite-adelic level-one subgroup of level $\top$) with two copies of the multiplicative measure `Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))` on $F_p^\times$ (the self-dual Haar measure restricted away from $0$, with density $\mathrm{modulus}^{-1}$, pulled back to the units), of $\bigl(\int^-_x G(\mathrm{unipotent}(x)\,\mathrm{diag}(a,d)\,k)\,dx\bigr)\cdot\mathrm{modulus}(d a^{-1})$, where $dx$ is the self-dual measure. Let $F$ lie in `principalSeries2 p lam`, i.e. $F$ is locally constant, invariant under left multiplication by upper unipotents, and satisfies $F(\mathrm{diag}(a)g)=\mathrm{torusChar2}(\mathrm{lam})(a)\,\mathrm{halfModulus2}(a)\,F(g)$ for diagonal $a$; and let $\Phi : M_2(F_p)\to\mathbb C$ be locally constant with compact support. Put $\phi(a,d)=\int_{k}F(k)\chi(\det k)\bigl(\int_x\Phi(\begin{pmatrix}a&x\\0&d\end{pmatrix}k)\,dx\bigr)d\mu_2(k)$, the outer integral over that level-one subgroup, and let $\hat\phi(x,y)=\int\!\!\int \phi(u,v)\,\psi_p(ux+vy)\,du\,dv$ for the standard local additive character $\psi_p$ and the product self-dual measure. The conclusion asserts the existence of $\sigma_\star\in\mathbb R$ such that for every $s$ with $\operatorname{Re} s>\sigma_\star$: the function $g\mapsto F({}^t g^{-1})\cdot(\mathrm{matFourier22}\ \psi_p\ \Phi)(g)\cdot\chi^{-1}(\det g)\cdot|\det g|^{s+3/2}$ is $\mu_2$-integrable; the function $(a,d)\mapsto\hat\phi(a,d)\,(\chi\,\mathrm{lam}\,0)^{-1}(a)\,(\chi\,\mathrm{lam}\,1)^{-1}(d)\,|a|^{1+s}|d|^{1+s}$ is integrable for the product multiplicative measure on $F_p^\times\times F_p^\times$; and `godementZeta2` at $p$, for the section $g\mapsto F({}^tg^{-1})$, the matrix Fourier transform $\mathrm{matFourier22}\ \psi_p\ \Phi$, the character $\chi^{-1}$ and the exponent $s+3/2$, equals $\kappa$ times the integral of that second function. Here $\mathrm{modulus}$ is the module of $F_p$ (the normalised absolute value), $|\cdot|^{w}$ denotes its complex power, ${}^tg^{-1}$ is `transposeInvN`, and $\mathrm{matFourier22}$ is the two-fold column Fourier transform on $M_2(F_p)$.
--
--   This is the local, contragredient half of Godement's unfolding for $GL_2$: the Godement–Jacquet zeta integral of the section $g\mapsto F({}^tg^{-1})$ against the matrix Fourier transform of $\Phi$ is identified, via Iwasawa decomposition and the Borel transformation law of the principal-series vector, with a two-variable Tate zeta integral of the Fourier transform of the unipotent slice $\phi$. It is used, together with its companion on the original side, by [`LanglandsTunnell.RankinSelberg.exists_gamma_forall_rational_godementZeta2_principalSeries2_and_clearedFE`](thm.html#LanglandsTunnell.RankinSelberg.exists_gamma_forall_rational_godementZeta2_principalSeries2_and_clearedFE) to produce the local functional equation with its gamma factor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_and_godementZeta2_transposeInv_matFourier22_eq_mul_twoVarZeta_fourierSlice_of_mem_principalSeries2.lean

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
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2

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

theorem LanglandsTunnell.RankinSelberg.exists_forall_integrable_and_godementZeta2_transposeInv_matFourier22_eq_mul_twoVarZeta_fourierSlice_of_mem_principalSeries2
    (p : HeightOneSpectrum (𝓞 ℚ))
    (lam : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i))
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure] (κ : ℝ), 0 < κ →
      (∀ G : GL (Fin 2) (p.adicCompletion ℚ) → ENNReal, Measurable G →
          ∫⁻ g, G g ∂μ₂ =
            ENNReal.ofReal κ *
              ∫⁻ q : GL (Fin 2) (p.adicCompletion ℚ) × ((p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ),
                (∫⁻ x : (p.adicCompletion ℚ), G (unipotent x * diagUnits2 q.2.1 q.2.2 * q.1) ∂(selfDualHaarAt ℚ p)) *
                  (modulus ((q.2.2 * q.2.1⁻¹ : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ENNReal)
                ∂((μ₂.restrict (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set (GL (Fin 2) (p.adicCompletion ℚ)))).prod
                  ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))))) →
      ∀ F ∈ principalSeries2 p lam,
      ∀ (Φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ), IsLocallyConstant Φ → HasCompactSupport Φ →
        let ϕ : (p.adicCompletion ℚ) × (p.adicCompletion ℚ) → ℂ := fun ad =>
          ∫ k in (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set (GL (Fin 2) (p.adicCompletion ℚ))),
            F k * ((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) *
              (∫ x : (p.adicCompletion ℚ), Φ (!![ad.1, x; 0, ad.2] * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) ∂(selfDualHaarAt ℚ p)) ∂μ₂
        let ϕhat : (p.adicCompletion ℚ) × (p.adicCompletion ℚ) → ℂ := fun xy =>
          ∫ uv : (p.adicCompletion ℚ) × (p.adicCompletion ℚ), ϕ uv * NumberField.StandardAddChar.psiLocal ℚ p (uv.1 * xy.1 + uv.2 * xy.2)
            ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))
        ∃ σd : ℝ, ∀ s : ℂ, σd < s.re →
          Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            F (transposeInvN (Fin 2) g) *
              matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
              ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 3 / 2)) μ₂ ∧
          Integrable (fun ad : (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ =>
            ϕhat ((ad.1 : (p.adicCompletion ℚ)), (ad.2 : (p.adicCompletion ℚ))) *
              (((χ * lam 0)⁻¹ ad.1 : ℂˣ) : ℂ) * (((χ * lam 1)⁻¹ ad.2 : ℂˣ) : ℂ) *
              ((modulus (ad.1 : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 + s) * ((modulus (ad.2 : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 + s))
            ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
          godementZeta2 p μ₂ (fun g : GL (Fin 2) (p.adicCompletion ℚ) => F (transposeInvN (Fin 2) g))
              (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ) χ⁻¹ (s + 3 / 2) =
            (κ : ℂ) *
              ∫ ad : (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ,
                ϕhat ((ad.1 : (p.adicCompletion ℚ)), (ad.2 : (p.adicCompletion ℚ))) *
                  (((χ * lam 0)⁻¹ ad.1 : ℂˣ) : ℂ) * (((χ * lam 1)⁻¹ ad.2 : ℂˣ) : ℂ) *
                  ((modulus (ad.1 : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 + s) * ((modulus (ad.2 : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 + s)
                ∂((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) := by sorry
