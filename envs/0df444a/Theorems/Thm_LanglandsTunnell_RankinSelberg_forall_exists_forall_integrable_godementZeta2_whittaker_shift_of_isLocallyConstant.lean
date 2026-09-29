-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_exists_forall_integrable_godementZeta2_whittaker_shift_of_isLocallyConstant
-- name    : LanglandsTunnell.RankinSelberg.forall_exists_forall_integrable_godementZeta2_whittaker_shift_of_isLocallyConstant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/d6907fa5-db6b-5416-bcb2-1798730688a9
-- title:
--   Uniform abscissa for local Godement–Jacquet Whittaker integrals
-- statement:
--   Fix a nonzero prime $p$ of $\mathcal O_{\mathbb Q}$ and write $F = \mathbb Q_p$ for the completion at $p$; let $\theta_0 : F^\times \to \mathbb C^\times$ be a group homomorphism, $N$ a nonzero ideal of $\mathcal O_{\mathbb Q}$, and $w_{2,\mathrm{base}} : \mathrm{GL}_2(F) \to \mathbb C$ a function subject to: the Whittaker transformation law $w_{2,\mathrm{base}}(u(x)g) = \psi_p(x)\, w_{2,\mathrm{base}}(g)$ for all $x \in F$ and $g$, where $u(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$ and $\psi_p$ is the standard adelic additive character composed with the embedding of $F$ into the adeles of $\mathbb Q$ at $p$; right invariance under the local level-one subgroup at $p$, namely the preimage under the embedding $\mathrm{GL}_2(F) \to \mathrm{GL}_2(\mathbb A_{\mathbb Q}^{\mathrm{fin}})$ of the finite level-$N$ subgroup; $w_{2,\mathrm{base}} \neq 0$; an irreducibility condition, that $w_{2,\mathrm{base}}$ lies in the span of the right translates of any nonzero element $w$ of the $\mathbb C$-span of the right translates $g \mapsto w_{2,\mathrm{base}}(gh)$; an admissibility condition, that for every open subgroup $U \le \mathrm{GL}_2(F)$ there is a finite set $B$ of functions whose span contains every right $U$-invariant element of that span; and the central character condition $w_{2,\mathrm{base}}(z\cdot g) = \theta_0(z)\, w_{2,\mathrm{base}}(g)$ for scalar matrices $z$. Let furthermore $\chi : F^\times \to \mathbb C^\times$ be a locally constant homomorphism. Then, with $F$ and $\mathrm{GL}_2(F)$ carrying their Borel measurable structures, for every Haar measure $\mu_2$ on $\mathrm{GL}_2(F)$, every $w$ in the span of the right translates of $w_{2,\mathrm{base}}$ and every $s_0 \in \mathbb C$ there exists a real $\sigma$ such that for all locally constant compactly supported $\Phi : M_2(F) \to \mathbb C$ and all $s$ with $\mathrm{Re}\, s > \sigma$, the function $g \mapsto w(g)\,\Phi(g)\,\chi(\det g)\,|\det g|^{s+s_0}$ is $\mu_2$-integrable, $|\cdot|$ being the module of $F$ given by the action of scalars on Haar measure.
--
--   This is the statement that the local Godement–Jacquet zeta integral attached to a Whittaker vector converges absolutely in a right half-plane whose abscissa may be chosen uniformly in the Schwartz–Bruhat function $\Phi$, strengthening the version in which $\sigma$ is allowed to depend on $\Phi$. It feeds the transpose-inverse variant of the same convergence statement and the assembly of the centre-cleared local functional equation for $\mathrm{GL}_2 \times \mathrm{GL}_2$ Rankin–Selberg integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_forall_exists_forall_integrable_godementZeta2_whittaker_shift_of_isLocallyConstant.lean

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
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open LanglandsTunnell.RankinSelberg

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

theorem LanglandsTunnell.RankinSelberg.forall_exists_forall_integrable_godementZeta2_whittaker_shift_of_isLocallyConstant
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
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∀ s₀ : ℂ,
          ∃ σ : ℝ, ∀ (Φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ), IsLocallyConstant Φ → HasCompactSupport Φ →
            ∀ s : ℂ, σ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                w g * Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
                  ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + s₀)) μ₂ := by sorry
