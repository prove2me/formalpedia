-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_exists_rational_godementZeta2_whittaker_shift
-- name    : LanglandsTunnell.RankinSelberg.forall_exists_rational_godementZeta2_whittaker_shift
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/a5bc15b9-9ed1-57ef-9d9c-b443d8f540ec
-- title:
--   Rationality in q^{-s} of local Godement zeta integrals
-- statement:
--   Fix a height-one prime $p$ of $\mathcal O_{\mathbb Q}$, write $F = \mathbb Q_p$ for the completion at $p$, and let $\theta_0 : F^\times \to \mathbb C^\times$ be a group homomorphism and $N \neq 0$ an ideal of $\mathcal O_{\mathbb Q}$. Let $w_{2,\mathrm{base}} : \mathrm{GL}_2(F) \to \mathbb C$ satisfy: the Whittaker transformation law $w_{2,\mathrm{base}}(u(x)g) = \psi_p(x)\, w_{2,\mathrm{base}}(g)$ for all $x \in F$ and $g$, where $u(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$ and $\psi_p$ is the local component at $p$ of the standard additive character of the adeles of $\mathbb Q$; right invariance under the subgroup $\mathrm{localLevelOne}$ of $\mathrm{GL}_2(F)$, the preimage under the local embedding $\mathrm{GL}_2(F) \to \mathrm{GL}_2(\mathbb A_{\mathbb Q}^{\mathrm{fin}})$ of the finite-adelic level-one subgroup of level $N$; $w_{2,\mathrm{base}} \neq 0$; an irreducibility condition, namely that for every nonzero $w$ in the $\mathbb C$-span $V$ of the right translates $g \mapsto w_{2,\mathrm{base}}(gh)$, the function $w_{2,\mathrm{base}}$ lies in the span of the right translates of $w$; an admissibility condition, namely that for every open subgroup $U \le \mathrm{GL}_2(F)$ there is a finite set $B$ of functions whose span contains every right-$U$-invariant element of $V$; and the central character law $w_{2,\mathrm{base}}(z \cdot g) = \theta_0(z)\, w_{2,\mathrm{base}}(g)$ for scalar matrices $z$. Let $\chi : F^\times \to \mathbb C^\times$ be a locally constant homomorphism. Then, $F$ and $\mathrm{GL}_2(F)$ being given their Borel measurable structures, for every Haar measure $\mu_2$ on $\mathrm{GL}_2(F)$, every $w \in V$, every locally constant compactly supported $\Phi : M_2(F) \to \mathbb C$ and every $s_0 \in \mathbb C$, there exist polynomials $P, Q \in \mathbb C[X]$ with $Q \neq 0$, an integer $m$ and a real $\sigma$ such that for all $s$ with $\operatorname{Re} s > \sigma$,
--   $$Z(w,\Phi,\chi; s+s_0)\, Q(q^{-s}) \;=\; q^{ms}\, P(q^{-s}), \qquad q = \#(\mathcal O_{\mathbb Q}/p),$$
--   where $Z(w,\Phi,\chi; s) = \int_{\mathrm{GL}_2(F)} w(g)\, \Phi(g)\, \chi(\det g)\, \lVert \det g \rVert^{s}\, d\mu_2(g)$ is `godementZeta2`, the modulus $\lVert\cdot\rVert$ being the distributive Haar character of $F$.
--
--   This is the local rationality statement for Godement–Jacquet zeta integrals of a $\mathrm{GL}_2$ Whittaker vector twisted by a quasi-character: the zeta integral, after the shift by $s_0$, becomes a rational function of $q^{-s}$ up to a monomial factor. It feeds the functional-equation and converse-theorem input at the finite place $p$ in the Langlands–Tunnell part of the argument, being used in the derivation of the rationality of the Godement zeta integral from the functional equations of the associated torus zeta integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_forall_exists_rational_godementZeta2_whittaker_shift.lean

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

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

theorem LanglandsTunnell.RankinSelberg.forall_exists_rational_godementZeta2_whittaker_shift
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
        ∀ (Φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ), IsLocallyConstant Φ → HasCompactSupport Φ →
        ∀ s₀ : ℂ,
          ∃ (P Q : Polynomial ℂ) (m : ℤ) (σ : ℝ), Q ≠ 0 ∧
            ∀ s : ℂ, σ < s.re →
              godementZeta2 p μ₂ w Φ χ (s + s₀) * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) := by sorry
