-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_and_dual_of_jacquetWhittaker3_ed2
-- name    : LanglandsTunnell.RankinSelberg.exists_rational_rsLocalIntegral_and_dual_of_jacquetWhittaker3_ed2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/f315d10a-3657-53e9-8461-78a05983ceb8
-- title:
--   Rationality of principal-series Rankin–Selberg local integrals at p
-- statement:
--   Fix a height-one prime $p$ of $\mathbb{Z}=\mathcal{O}_{\mathbb{Q}}$, write $\mathbb{Q}_p$ for the completion and $\psi_p=$ `psiLocal` $\mathbb{Q}\,p$ for the component at $p$ of the standard adelic additive character. Let $\lambda_0,\lambda_1,\lambda_2$ be locally constant characters $\mathbb{Q}_p^{\times}\to\mathbb{C}^{\times}$, let $\Phi$ be a locally constant, compactly supported function on $\mathbb{Q}_p^{3}$, let $x,y,z\in\mathbb{Q}_p$, and let $W_3(h)=$ `jacquetWhittaker3` $p\,\lambda\,\Phi$ evaluated at $\mathrm{diag}(1,-1,1)\,h\,u(x,y,z)\,w$, where `jacquetWhittaker3` is the stabilised truncated unipotent average (`jacquetValue`) of the right translate of the big-cell section `cellSectionOf` attached to $\lambda,\Phi$, $u(x,y,z)$ is the upper unipotent matrix with entries $x,y,z$ and $w$ the $3\times3$ antidiagonal permutation matrix. On the $GL_2$ side, let $\theta_0$ be a character of $\mathbb{Q}_p^{\times}$, $N\neq 0$ an ideal of $\mathcal{O}_{\mathbb{Q}}$, and $w_{2,\mathrm{base}}:GL_2(\mathbb{Q}_p)\to\mathbb{C}$ a nonzero function satisfying: $w_{2,\mathrm{base}}(u(x)g)=\psi_p(x)w_{2,\mathrm{base}}(g)$ for unipotent $u(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$; right invariance under the local level-one subgroup at $p$ for $N$ (the preimage under the embedding at $p$ of the adelic subgroup `finiteLevelOne`); the irreducibility condition that every nonzero $w$ in the span $V$ of the right translates of $w_{2,\mathrm{base}}$ has $w_{2,\mathrm{base}}$ in the span of the right translates of $w$; admissibility, namely for each open subgroup $U$ a finite set $B$ spanning the $U$-right-invariant vectors of $V$; and the central character law $w_{2,\mathrm{base}}(zI\cdot g)=\theta_0(z)w_{2,\mathrm{base}}(g)$. Let $w_{0,p}\in GL_2(\mathbb{Q}_p)$ have matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$. Then, with $GL_2(\mathbb{Q}_p)$ carrying its Borel structure, for every Haar measure $\mu_2$ on $GL_2(\mathbb{Q}_p)$, every Haar measure $\mu_{N_2}$ on the image $N$ of `unipotentGL2Hom` (the upper unipotent subgroup), and every $w_2\in V$, there are polynomials $P,P_d,Q,Q_d\in\mathbb{C}[X]$, integers $m,m_d$ and reals $\sigma_2,\sigma_3$ with $Q\neq0$, $Q_d\neq0$ such that, for the measure $\mu_2$ weighted by the quotient density [`HaarQuotient.density`](def/HaarQuotient.html#L25) of $N$ with respect to $\mu_{N_2}$: for $\operatorname{Re}s>\sigma_2$ the function $g\mapsto W_3(\iota g)\,w_2(g)\,|\det g|^{\,s-1/2}$ is integrable, and the Rankin–Selberg integral `rsLocalIntegral` of the pair $(W_3\circ\iota,\,w_2)$ against $|\det\cdot|$ at $s$ satisfies $\Psi(s)\,Q(q^{-s})=q^{ms}P(q^{-s})$ with $q=\mathrm{absNorm}(p)$; and for $\operatorname{Re}s>\sigma_3$ the same two assertions hold, with $Q_d,m_d,P_d$, for the dual pair consisting of $g\mapsto W_3(w_\ell\,{}^{t}(\iota g)^{-1})$ (the function `dualWhittakerFn3` applied to $W_3$ and composed with the block embedding $\iota=$ `iotaGL`) and $g\mapsto |\det g|\,w_2(w_{0,p}\,{}^{t}g^{-1})$. Here $|\cdot|$ is the module `modulus` of $\mathbb{Q}_p$ and $w_\ell$ the long Weyl element of $GL_3$.
--
--   This is the local rationality statement for $GL_3\times GL_2$ Rankin–Selberg integrals in the style of Jacquet–Piatetski-Shapiro–Shalika, specialised to a $GL_3$ Whittaker function obtained from a Jacquet integral on a principal series $I(\lambda)$ with no unitarity imposed on the inducing characters, paired against a vector in the Whittaker model of an irreducible admissible generic representation of $GL_2(\mathbb{Q}_p)$ with central character $\theta_0$ and level $N$. It feeds the principal-series rationality statement [`LanglandsTunnell.RankinSelberg.exists_rational_rsLocalIntegral_and_dual_of_principalSeries3`](thm.html#LanglandsTunnell.RankinSelberg.exists_rational_rsLocalIntegral_and_dual_of_principalSeries3) and the cleared functional-equation product [`LanglandsTunnell.RankinSelberg.forall_rsLocalIntegral_clearedFE_prod_of_jacquetWhittaker3_of_forall_torusZeta_fe`](thm.html#LanglandsTunnell.RankinSelberg.forall_rsLocalIntegral_clearedFE_prod_of_jacquetWhittaker3_of_forall_torusZeta_fe).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_and_dual_of_jacquetWhittaker3_ed2.lean

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
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

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

theorem LanglandsTunnell.RankinSelberg.exists_rational_rsLocalIntegral_and_dual_of_jacquetWhittaker3_ed2
    (p : HeightOneSpectrum (𝓞 ℚ))

    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i))
    (Φ : (Fin 3 → p.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (x y z : p.adicCompletion ℚ)
    (W₃ : LocalGL3 p → ℂ)
    (hW₃ : W₃ = fun h => jacquetWhittaker3 p lam Φ
      (diagonal3 p ![1, -1, 1] * h * (upperUnipotent3 x y z * antidiagonal3 p)))

    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    :
      letI := localGLBorel ℚ p
      haveI := borelSpace_localGLBorel ℚ p
      ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
          (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
        ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          ∃ (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ), Q ≠ 0 ∧ Qd ≠ 0 ∧

            (∀ s : ℂ, σ₂ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (W₃ (iotaGL g) * w₂ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) ∧
            (∀ s : ℂ, σ₃ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (dualWhittakerFn3 W₃ (iotaGL g) * (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) ∧

            (∀ s : ℂ, σ₂ < s.re →
              RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                  (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                  s (fun g => W₃ (iotaGL g)) w₂ * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
            (∀ s : ℂ, σ₃ < s.re →
              RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                  (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                  s (fun g => dualWhittakerFn3 W₃ (iotaGL g)) (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) * Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) := by sorry
