-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_exists_laurent_godementZeta2_whittaker_shift_of_torusLaurent
-- name    : LanglandsTunnell.RankinSelberg.forall_exists_laurent_godementZeta2_whittaker_shift_of_torusLaurent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/a4bae08c-0f54-5c6f-965c-8764e6c9dbf2
-- title:
--   Laurent polynomiality of shifted Godement–Jacquet zeta integrals
-- statement:
--   Fix a finite place $p$ of $\mathbb{Q}$, i.e. a height-one prime of $\mathcal{O}_{\mathbb{Q}}$, write $F = \mathbb{Q}_p$ for the completion and $q =$ `Ideal.absNorm p.asIdeal`. Let $\theta_0 : F^\times \to \mathbb{C}^\times$ be a multiplicative character, $N \neq 0$ an ideal of $\mathcal{O}_{\mathbb{Q}}$, and let $w_{2\mathrm{base}} : \mathrm{GL}_2(F) \to \mathbb{C}$ satisfy: the Whittaker transformation law $w_{2\mathrm{base}}(u(x)g) = \psi_p(x)\,w_{2\mathrm{base}}(g)$ for the upper unipotent $u(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$ and the local component $\psi_p$ at $p$ of the standard adelic additive character; right invariance under the local level-one subgroup at $p$ of level $N$ (the pullback along the local embedding of the finite-adelic level-one subgroup); $w_{2\mathrm{base}} \neq 0$; an irreducibility condition, namely every nonzero $w$ in the span $V$ of the right translates $g \mapsto w_{2\mathrm{base}}(gh)$ has $w_{2\mathrm{base}}$ in the span of its own right translates; an admissibility condition, namely for each open subgroup $U \le \mathrm{GL}_2(F)$ there is a finite set $B$ of functions spanning all right $U$-invariant elements of $V$; and the central character law $w_{2\mathrm{base}}(z\cdot g) = \theta_0(z)w_{2\mathrm{base}}(g)$ for scalar matrices. Let $\chi : F^\times \to \mathbb{C}^\times$ be a locally constant character. Assume the torus hypothesis: for every $w \in V$ there are a polynomial $P$, an integer $m$ and $\sigma_0 \in \mathbb{R}$ such that for $\mathrm{Re}\,s > \sigma_0$ the function $y \mapsto w(\mathrm{diag}(y,1))\,\chi(y)\,|y|^{s-1/2}$ is integrable for the multiplicative measure induced on $F^\times$ by the self-dual additive Haar measure at $p$, with integral $q^{ms}P(q^{-s})$, the absolute value being the module $\mathrm{modulus}$. The conclusion asserts: for every Haar measure $\mu_2$ on $\mathrm{GL}_2(F)$ (with its Borel structure), every $w \in V$, every locally constant compactly supported $\Phi$ on $M_2(F)$ and every shift $s_0 \in \mathbb{C}$, there are a polynomial $P$, an integer $m$ and $\sigma \in \mathbb{R}$ such that for all $s$ with $\mathrm{Re}\,s > \sigma$ the Godement–Jacquet integral $\int_{\mathrm{GL}_2(F)} w(g)\,\Phi(g)\,\chi(\det g)\,|\det g|^{s+s_0}\,d\mu_2(g)$ equals $q^{ms}P(q^{-s})$.
--
--   This is the local rationality statement for Godement–Jacquet zeta integrals of Whittaker vectors in an irreducible admissible generic representation of $\mathrm{GL}_2(\mathbb{Q}_p)$: such integrals, after an arbitrary shift of the spectral variable, are Laurent polynomials in $q^{-s}$, deduced from the corresponding property of the one-dimensional torus integrals. It feeds the local input of the converse-theorem package, being used in the passage from torus zeta functional equations to the meromorphic continuation and functional equation of the $\mathrm{GL}_2$ zeta integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_forall_exists_laurent_godementZeta2_whittaker_shift_of_torusLaurent.lean

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

open IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open AutomorphicForm
open LanglandsTunnell.RankinSelberg

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

theorem LanglandsTunnell.RankinSelberg.forall_exists_laurent_godementZeta2_whittaker_shift_of_torusLaurent
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
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)

    (htorus : letI := localBorel ℚ p
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ (P : Polynomial ℂ) (m : ℤ) (σ₀ : ℝ),
        ∀ s : ℂ, σ₀ < s.re →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))
    :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∀ (Φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ), IsLocallyConstant Φ → HasCompactSupport Φ →
        ∀ s₀ : ℂ,
          ∃ (P : Polynomial ℂ) (m : ℤ) (σ : ℝ),
            ∀ s : ℂ, σ < s.re →
              godementZeta2 p μ₂ w Φ χ (s + s₀) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) := by sorry
