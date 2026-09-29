-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_schwartz_godementZeta2_whittaker_eq_mul_torusZeta_and_dual_of_integrable
-- name    : LanglandsTunnell.RankinSelberg.exists_schwartz_godementZeta2_whittaker_eq_mul_torusZeta_and_dual_of_integrable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/43a13c58-fae0-5326-8962-9c0f254c24ab
-- title:
--   Local test function matching Godement–Jacquet and torus zeta integrals
-- statement:
--   Let $p$ be a height-one prime of $\mathcal O_{\mathbb Q}$, write $F=\mathbb Q_p$ for the completion $p.\mathrm{adicCompletion}\,\mathbb Q$, let $\theta_0,\chi\colon F^\times\to\mathbb C^\times$ be multiplicative characters with $\chi$ locally constant, and let $N\neq 0$ be an ideal of $\mathcal O_{\mathbb Q}$. Let $w_2^{\mathrm{base}}\colon \mathrm{GL}_2(F)\to\mathbb C$ be non-zero and satisfy: $w_2^{\mathrm{base}}(\mathrm{unipotent}(x)\,g)=\psi_p(x)\,w_2^{\mathrm{base}}(g)$ for the local standard additive character `psiLocal`, where $\mathrm{unipotent}(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$; right invariance under the subgroup `localLevelOne` obtained by pulling back the finite adelic level-$N$ group along the embedding of $\mathrm{GL}_2(F)$ into $\mathrm{GL}_2$ of the finite adeles; and $w_2^{\mathrm{base}}(\mathrm{scalar}(z)g)=\theta_0(z)w_2^{\mathrm{base}}(g)$. Let $w_J\in\mathrm{GL}_2(F)$ have matrix $\begin{pmatrix}0&1\\-1&0\end{pmatrix}$. Then, with the Borel structures on $F$ and on $\mathrm{GL}_2(F)$, for every Haar measure $\mu_2$ on $\mathrm{GL}_2(F)$ and every $w$ in the $\mathbb C$-span of the right translates $g\mapsto w_2^{\mathrm{base}}(gh)$, there are a locally constant, compactly supported $\Phi_0\colon M_2(F)\to\mathbb C$ and a constant $C\neq 0$ such that for all $s\in\mathbb C$ the following hold, the multiplicative measure on $F^\times$ being the pullback along $F^\times\hookrightarrow F$ of $|x|^{-1}$ times the self-dual additive Haar measure, and $|\cdot|=\mathrm{modulus}$ the module of the local field. First, if $y\mapsto w(\mathrm{diag}(y,1))\chi(y)|y|^{s-1/2}$ is integrable, then $g\mapsto w(g)\Phi_0(g)\chi(\det g)|\det g|^{s+1/2}$ is $\mu_2$-integrable and $\mathrm{godementZeta2}$ of $(w,\Phi_0,\chi)$ at $s+1/2$, namely $\int w(g)\Phi_0(g)\chi(\det g)|\det g|^{s+1/2}\,d\mu_2$, equals $C$ times $\int_{F^\times} w(\mathrm{diag}(y,1))\chi(y)|y|^{s-1/2}$. Second, if $g\mapsto w({}^t g^{-1})\,\widehat{\Phi_0}(g)\,\chi^{-1}(\det g)|\det g|^{s+3/2}$ is $\mu_2$-integrable, where $\widehat{\Phi_0}=\mathrm{matFourier22}$ is the iterated column Fourier transform of $\Phi_0$ with respect to `psiLocal` and the self-dual measure, then $y\mapsto w(\mathrm{diag}(y,1)w_J)\chi(y)^{-1}\theta_0(y)^{-1}|y|^{1/2+s}$ is integrable and $\mathrm{godementZeta2}$ of $(w\circ{}^t(\cdot)^{-1},\widehat{\Phi_0},\chi^{-1})$ at $s+3/2$ equals $C$ times $\int_{F^\times} w(\mathrm{diag}(y,1)w_J)\chi(y)^{-1}\theta_0(y)^{-1}|y|^{1/2+s}$. Here $\mathrm{diag}(y,1)$ denotes `diagOne y`, and the two integrability hypotheses are the stated directions: group-side for the first clause derived from torus-side, torus-side for the second derived from group-side.
--
--   This is the local comparison, at a finite place, between Godement–Jacquet zeta integrals on $\mathrm{GL}_2$ with a matrix test function and the $\mathrm{GL}_2\times\mathrm{GL}_1$ torus (Hecke–Jacquet–Langlands) zeta integrals of a Whittaker vector and of its reflection by $w_J$, with one and the same non-zero proportionality constant on both the original and the Fourier-dual side. It feeds the deduction of the functional equation for the torus zeta integrals from that for the Godement–Jacquet integrals in the converse-theorem input to the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_schwartz_godementZeta2_whittaker_eq_mul_torusZeta_and_dual_of_integrable.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_schwartz_godementZeta2_whittaker_eq_mul_torusZeta_and_dual_of_integrable
    (p : HeightOneSpectrum (𝓞 ℚ))
    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (wJ : GL (Fin 2) (p.adicCompletion ℚ)) (hwJ : (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; -1, 0])
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∃ Φ₀ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ, IsLocallyConstant Φ₀ ∧ HasCompactSupport Φ₀ ∧
          ∃ C : ℂ, C ≠ 0 ∧
            (∀ s : ℂ,
              Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
                w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                w g * Φ₀ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
                  ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2)) μ₂ ∧
              godementZeta2 p μ₂ w Φ₀ χ (s + 1 / 2) =
                C * ∫ y : (p.adicCompletion ℚ)ˣ,
                  w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
            (∀ s : ℂ,
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                w (transposeInvN (Fin 2) g) *
                  matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ₀ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
                  ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
                  ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 3 / 2)) μ₂ →
              Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
                w (diagOne y * wJ) * (((χ y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                  ((modulus (y : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 / 2 + s)) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
              godementZeta2 p μ₂ (fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (transposeInvN (Fin 2) g))
                  (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ₀) χ⁻¹ (s + 3 / 2) =
                C * ∫ y : (p.adicCompletion ℚ)ˣ,
                  w (diagOne y * wJ) * (((χ y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                    ((modulus (y : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 / 2 + s) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) := by sorry
