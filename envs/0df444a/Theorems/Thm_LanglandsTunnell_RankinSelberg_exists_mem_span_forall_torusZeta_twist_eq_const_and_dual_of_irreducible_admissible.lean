-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_mem_span_forall_torusZeta_twist_eq_const_and_dual_of_irreducible_admissible
-- name    : LanglandsTunnell.RankinSelberg.exists_mem_span_forall_torusZeta_twist_eq_const_and_dual_of_irreducible_admissible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/929e318c-2118-50c0-be13-ed737bf31d3b
-- title:
--   Constant η-twisted local torus zeta integrals for Whittaker models
-- statement:
--   Fix a height-one prime $p$ of $\mathcal O_{\mathbb Q}$, a character $\theta_0 : (\mathbb Q_p)^\times \to \mathbb C^\times$ (a monoid homomorphism on the units of the completion $p.\mathrm{adicCompletion}\ \mathbb Q$), a nonzero ideal $N$ of $\mathcal O_{\mathbb Q}$, and a function $w_{2\mathrm{base}} : GL_2(\mathbb Q_p) \to \mathbb C$ subject to: (i) $w_{2\mathrm{base}}(u(x)g) = \psi_p(x)\,w_{2\mathrm{base}}(g)$ for all $x$ and $g$, where $u(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$ and $\psi_p$ is the local component `psiLocal` of the standard adelic additive character; (ii) right invariance under [`AdelicDock.localLevelOne`](def/AdelicDock_LocalEmbedding.html#L178), the pullback along the local embedding $GL_2(\mathbb Q_p) \to GL_2(\mathbb A_{\mathbb Q}^{\mathrm{fin}})$ of the level-one congruence subgroup of level $N$; (iii) $w_{2\mathrm{base}} \neq 0$; (iv) cyclicity: every nonzero $w$ in the span $V$ of the right translates $g \mapsto w_{2\mathrm{base}}(gh)$ has $w_{2\mathrm{base}}$ in the span of its own right translates; (v) admissibility: for each open subgroup $U$ there is a finite set $B$ of functions spanning all $U$-right-invariant elements of $V$; (vi) central character: $w_{2\mathrm{base}}(zI\cdot g) = \theta_0(z)w_{2\mathrm{base}}(g)$. Fix further $w_J \in GL_2(\mathbb Q_p)$ with matrix $\begin{pmatrix}0&1\\-1&0\end{pmatrix}$ and a locally constant character $\eta : (\mathbb Q_p)^\times \to \mathbb C^\times$. Then, for the Borel structure on the completion, there exist nonzero constants $c, c^\vee \in \mathbb C$ and vectors $w_1, w_2 \in V$ such that for every $s \in \mathbb C$ both integrands below are integrable for the multiplicative measure on $(\mathbb Q_p)^\times$ obtained by pulling back along $y \mapsto y$ the density $|x|^{-1}$ times the self-dual additive Haar measure `selfDualHaarAt` off $0$, and $$\int w_1\!\begin{pmatrix}y&0\\0&1\end{pmatrix}\eta(y)\,|y|^{s-1/2}\,d^\times y = c, \qquad \int w_2\!\left(\begin{pmatrix}y&0\\0&1\end{pmatrix}w_J\right)\eta(y)^{-1}\theta_0(y)^{-1}|y|^{1/2-s}\,d^\times y = c^\vee,$$ where $|\cdot|$ is `modulus` and $\begin{pmatrix}y&0\\0&1\end{pmatrix}$ is `diagOne y`.
--
--   This is the local "bump vector" statement: in the Kirillov realisation of an irreducible admissible generic representation of $GL_2(\mathbb Q_p)$ with central character $\theta_0$, one may choose vectors whose $\eta$-twisted torus zeta integral, and whose dual zeta integral, are nonzero constants independent of $s$. It feeds the local functional equation and the rationality of torus zeta integrals used in the Rankin–Selberg and converse-theorem steps, being cited by the results on cuspidal torus integrals, on rational $\eta$-twisted functional equations, and on cleared functional equations for Godement–Whittaker zeta integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_mem_span_forall_torusZeta_twist_eq_const_and_dual_of_irreducible_admissible.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_mem_span_forall_torusZeta_twist_eq_const_and_dual_of_irreducible_admissible
    (p : HeightOneSpectrum (𝓞 ℚ))
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
    (wJ : GL (Fin 2) (p.adicCompletion ℚ)) (hwJ : (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; -1, 0])

    (η : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hη : IsLocallyConstant η) :
    letI := localBorel ℚ p
    ∃ (c cd : ℂ), c ≠ 0 ∧ cd ≠ 0 ∧
      (∃ w₁ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∀ s : ℂ,
          Integrable (fun y : (p.adicCompletion ℚ)ˣ => w₁ (diagOne y) * ((η y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
          (∫ y : (p.adicCompletion ℚ)ˣ, w₁ (diagOne y) * ((η y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) = c) ∧
      (∃ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∀ s : ℂ,
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
              w₂ (diagOne y * wJ) * (((η y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
          (∫ y : (p.adicCompletion ℚ)ˣ,
                w₂ (diagOne y * wJ) * (((η y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) = cd) := by sorry
