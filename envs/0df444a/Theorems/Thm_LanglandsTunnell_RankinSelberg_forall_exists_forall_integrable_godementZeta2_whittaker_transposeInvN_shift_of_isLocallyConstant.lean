-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_exists_forall_integrable_godementZeta2_whittaker_transposeInvN_shift_of_isLocallyConstant
-- name    : LanglandsTunnell.RankinSelberg.forall_exists_forall_integrable_godementZeta2_whittaker_transposeInvN_shift_of_isLocallyConstant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/bb3f67ef-8dd3-500f-bcce-749f907bafdd
-- title:
--   Uniform integrability of dual local Godement–Jacquet integrals
-- statement:
--   Fix a height one prime $p$ of $\mathcal O_{\mathbb Q}$, a homomorphism $\theta_0 : (\mathbb Q_p)^\times \to \mathbb C^\times$ (writing $\mathbb Q_p$ for `p.adicCompletion ℚ`), a nonzero ideal $N \subseteq \mathcal O_{\mathbb Q}$, and a function $w_2 : \mathrm{GL}_2(\mathbb Q_p) \to \mathbb C$ subject to: the Whittaker law $w_2\big(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\big)g) = \psi_p(x)\,w_2(g)$ for the local component $\psi_p$ of the standard adelic additive character; right invariance under the subgroup [`AdelicDock.localLevelOne`](def/AdelicDock_LocalEmbedding.html#L178) of $\mathrm{GL}_2(\mathbb Q_p)$, the preimage under the local embedding into $\mathrm{GL}_2$ of the finite adeles of the level-one-at-$N$ subgroup; $w_2 \neq 0$; an irreducibility hypothesis, namely that every nonzero $w$ in the $\mathbb C$-span $V$ of the right translates $g \mapsto w_2(gh)$ has $w_2$ in the span of its own right translates; an admissibility hypothesis, namely that for each open subgroup $U$ there is a finite set $B$ of functions whose span contains all right $U$-invariant elements of $V$; and the central character law $w_2(z\cdot 1_2 \cdot g) = \theta_0(z) w_2(g)$. Let $\chi : (\mathbb Q_p)^\times \to \mathbb C^\times$ be a locally constant homomorphism. Then, with the Borel $\sigma$-algebras on $\mathbb Q_p$ and on $\mathrm{GL}_2(\mathbb Q_p)$, for every Haar measure $\mu_2$ on $\mathrm{GL}_2(\mathbb Q_p)$, every $w \in V$ and every $s_0 \in \mathbb C$, there exists $\sigma \in \mathbb R$ such that for every locally constant, compactly supported $\Psi : M_2(\mathbb Q_p) \to \mathbb C$ and every $s$ with $\mathrm{Re}\,s > \sigma$, the function $g \mapsto w({}^t g^{-1})\,\Psi(g)\,\chi^{-1}(\det g)\,|\det g|^{s+s_0}$ is $\mu_2$-integrable, where ${}^t g^{-1}$ is `transposeInvN` and $|\cdot|$ is the modulus given by the distributive Haar character.
--
--   This is the absolute convergence, in a right half-plane, of the local Godement–Jacquet zeta integral attached to a Whittaker vector evaluated at the transpose-inverse argument; the point of the statement is that the abscissa $\sigma$ depends only on $w$ and the shift $s_0$, not on the test function $\Psi$. It feeds the construction of the local Rankin–Selberg integral and its Laurent-type functional equation for principal series.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_forall_exists_forall_integrable_godementZeta2_whittaker_transposeInvN_shift_of_isLocallyConstant.lean

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

theorem LanglandsTunnell.RankinSelberg.forall_exists_forall_integrable_godementZeta2_whittaker_transposeInvN_shift_of_isLocallyConstant
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
          ∃ σ : ℝ, ∀ (Ψ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ), IsLocallyConstant Ψ → HasCompactSupport Ψ →
            ∀ s : ℂ, σ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                w (transposeInvN (Fin 2) g) * Ψ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
                  ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
                  ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + s₀)) μ₂ := by sorry
