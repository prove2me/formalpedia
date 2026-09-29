-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_exists_integrable_godementZeta2_whittaker_transposeInvN_shift
-- name    : LanglandsTunnell.RankinSelberg.forall_exists_integrable_godementZeta2_whittaker_transposeInvN_shift
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/704a93b9-8e86-56d5-a476-3879978e1d18
-- title:
--   Integrability of the dual local Godement–Jacquet zeta integrand
-- statement:
--   Let $p$ be a height-one prime of $\mathcal O_{\mathbb Q}$, write $F = \mathbb Q_p$ for the completion of $\mathbb Q$ at $p$, let $\theta_0 : F^\times \to \mathbb C^\times$ be a group homomorphism, and let $N \neq 0$ be an ideal of $\mathcal O_{\mathbb Q}$. Let $w_{2,\mathrm{base}} : \mathrm{GL}_2(F) \to \mathbb C$ satisfy: the Whittaker law $w_{2,\mathrm{base}}\bigl(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\bigr) g) = \psi_p(x)\, w_{2,\mathrm{base}}(g)$ for all $x \in F$ and $g$, where $\psi_p$ is the $p$-component `psiLocal` of the standard adelic additive character of $\mathbb Q$; right invariance under `localLevelOne`, the preimage under the local embedding $\mathrm{GL}_2(F) \hookrightarrow \mathrm{GL}_2(\mathbb A_{\mathbb Q}^{\mathrm{fin}})$ of the finite-adelic level-$N$ subgroup `finiteLevelOne`; non-vanishing, $w_{2,\mathrm{base}} \neq 0$; the irreducibility condition that every nonzero $w$ in the span $V$ of the right translates $g \mapsto w_{2,\mathrm{base}}(gh)$ has $w_{2,\mathrm{base}}$ in the span of the right translates of $w$; the admissibility condition that for every open subgroup $U \le \mathrm{GL}_2(F)$ there is a finite set $B$ of functions such that every $U$-right-invariant $w \in V$ lies in the $\mathbb C$-span of $B$; and the central character law $w_{2,\mathrm{base}}(z\cdot g) = \theta_0(z)\, w_{2,\mathrm{base}}(g)$ for scalar matrices $z \in F^\times$. Let $\chi : F^\times \to \mathbb C^\times$ be a locally constant homomorphism. Then, with the Borel structures on $F$ and on $\mathrm{GL}_2(F)$, for every Haar measure $\mu_2$ on $\mathrm{GL}_2(F)$, every $w \in V$, every locally constant $\Psi : M_2(F) \to \mathbb C$ of compact support, and every $s_0 \in \mathbb C$, there exists $\sigma \in \mathbb R$ such that for all $s$ with $\mathrm{Re}\, s > \sigma$ the function $$g \longmapsto w\bigl({}^t(g^{-1})\bigr)\, \Psi(g)\, \chi(\det g)^{-1}\, \lvert \det g\rvert^{\,s+s_0}$$ is $\mu_2$-integrable, where ${}^t(g^{-1})$ is `transposeInvN` and $\lvert\cdot\rvert$ is the module `modulus` given by the scaling factor of Haar measure on $F$.
--
--   This is the convergence statement for the integrand of the dual local zeta integral in the Godement–Jacquet functional equation at $p$, with the Fourier transform of a test function replaced by an arbitrary locally constant compactly supported $\Psi$ on $M_2(F)$ and with a free shift $s_0$ (consumers take $s_0 = 3/2$). It supplies one of the hypotheses of the local cleared functional equation [`LanglandsTunnell.RankinSelberg.forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_borelEigenfunctional`](thm.html#LanglandsTunnell.RankinSelberg.forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_borelEigenfunctional), and is deduced from the corresponding statement `forall_exists_integrable_godementZeta2_whittaker_shift` for $w$ itself.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_forall_exists_integrable_godementZeta2_whittaker_transposeInvN_shift.lean

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

theorem LanglandsTunnell.RankinSelberg.forall_exists_integrable_godementZeta2_whittaker_transposeInvN_shift
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
        ∀ (Ψ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ), IsLocallyConstant Ψ → HasCompactSupport Ψ →
        ∀ s₀ : ℂ,
          ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              w (transposeInvN (Fin 2) g) * Ψ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
                ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + s₀)) μ₂ := by sorry
