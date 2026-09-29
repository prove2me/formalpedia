-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_setIntegral_units_apply_diagUnitGL2_mul_weylJ_eq_mul_setIntegral_of_cuspidal
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_setIntegral_units_apply_diagUnitGL2_mul_weylJ_eq_mul_setIntegral_of_cuspidal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/ab16b491-2609-554d-b130-c6f4cdfd6ce6
-- title:
--   Weyl element on shells: twisted local functional equation
-- statement:
--   Let $p$ be a non-zero prime of the ring of integers of $\mathbb{Q}$, write $F$ for the completion $\mathbb{Q}_p$ and let $\varpi$ be an element of its valuation ring whose image in $F$ is non-zero and has valuation $\exp(-1)$, i.e. a uniformiser; let $\theta_0 \colon F^\times \to \mathbb{C}^\times$ be a multiplicative character, and let $N$ be a non-zero ideal. Let $w_{2} \colon \mathrm{GL}_2(F) \to \mathbb{C}$ be a function satisfying: the Whittaker law $w_2\bigl(\binom{1\ x}{0\ 1} g\bigr) = \psi_p(x)\, w_2(g)$, where $\psi_p$ is the local component at $p$ of the standard additive character of the adeles of $\mathbb{Q}$; right invariance under the subgroup $\mathrm{localLevelOne}$, the preimage under the local embedding $\mathrm{GL}_2(F)\to\mathrm{GL}_2(\mathbb{A}_f)$ of the level-$N$ group of matrices congruent to a level-one matrix together with their inverses; $w_2 \neq 0$; an irreducibility hypothesis, namely that every non-zero element $w$ of the span $V$ of the right translates $g \mapsto w_2(gh)$ has $w_2$ in the span of its own right translates; an admissibility hypothesis, namely that for each open subgroup $U \le \mathrm{GL}_2(F)$ there is a finite family spanning the right $U$-invariant vectors of $V$; and the central character law $w_2(z\cdot g) = \theta_0(z)\,w_2(g)$ for scalar matrices $z$. Let $w_J \in \mathrm{GL}_2(F)$ have matrix $\begin{pmatrix}0&1\\-1&0\end{pmatrix}$. Cuspidality is assumed per vector: every $v \in V$ admits $N_0 \in \mathbb{Z}$ with $v(\mathrm{diag}(y,1)) = 0$ for all units $y$ with $|y| \le \exp(N_0)$. Finally let $\eta \colon F^\times \to \mathbb{C}^\times$ be a character having conductor exponent $c_\eta$, in the sense that $\eta$ is trivial on the $c_\eta$-th higher unit group and, for each $m < c_\eta$, non-trivial on the $m$-th one. Then, $F$ being given its Borel $\sigma$-algebra, for every Haar measure $\nu$ on $F^\times$ there exist $E_\eta \in \mathbb{C}$, $E_\eta \neq 0$, and $e_\eta \in \mathbb{Z}$ such that for all $w \in V$ and all $n \in \mathbb{Z}$,
--   $$\int_{|u|=1} w\bigl(\mathrm{diag}(\varpi^{n}u,1)\, w_J\bigr)\,\eta(u)^{-1}\theta_0(u)^{-1}\,d\nu(u) = E_\eta\,\theta_0(\varpi)^{n}\int_{|u|=1} w\bigl(\mathrm{diag}(\varpi^{\,e_\eta-n}u,1)\bigr)\,\eta(u)\,d\nu(u),$$
--   the diagonal matrices being the units with matrix $\begin{pmatrix}x&0\\0&1\end{pmatrix}$.
--
--   This is the shell-by-shell, Mellin-inverted form of the local functional equation for the twist by $\eta$ of a cuspidal generic representation of $\mathrm{GL}_2(\mathbb{Q}_p)$ realised in its Whittaker model: the action of the Weyl element $w_J$ on the shell coefficients of the associated Kirillov functions is given by a single non-zero constant $E_\eta$ and a shift $n \mapsto e_\eta - n$. It is used in the local Rankin–Selberg part of the Langlands–Tunnell development, where it feeds the identification of the Kirillov-model pairing under translation and the Fourier-type expansion of Kirillov functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_setIntegral_units_apply_diagUnitGL2_mul_weylJ_eq_mul_setIntegral_of_cuspidal.lean

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

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.RankinSelberg
open MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

theorem LanglandsTunnell.RankinSelberg.exists_forall_setIntegral_units_apply_diagUnitGL2_mul_weylJ_eq_mul_setIntegral_of_cuspidal
    (p : HeightOneSpectrum (𝓞 ℚ))
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
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

    (hcusp : ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ N₀ : ℤ, ∀ y : (p.adicCompletion ℚ)ˣ, Valued.v (y : (p.adicCompletion ℚ)) ≤ WithZero.exp N₀ → v (diagOne y) = 0)

    (η : (p.adicCompletion ℚ)ˣ →* ℂˣ) (cη : ℕ) (hη : HasConductorExponentAt ℚ p η cη) :
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    ∀ (ν : Measure (p.adicCompletion ℚ)ˣ) [ν.IsHaarMeasure],
      ∃ (Eη : ℂ) (eη : ℤ), Eη ≠ 0 ∧
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ∀ n : ℤ,
          ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
              w (diagUnitGL2 ((Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ n * u) * wJ) * ((((η u : ℂˣ) : ℂ))⁻¹ * (((θ₀ u : ℂˣ) : ℂ))⁻¹) ∂ν =
            Eη * (((θ₀ (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)) ^ n *
              ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
                w (diagUnitGL2 ((Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ (eη - n) * u)) * ((η u : ℂˣ) : ℂ) ∂ν := by sorry
