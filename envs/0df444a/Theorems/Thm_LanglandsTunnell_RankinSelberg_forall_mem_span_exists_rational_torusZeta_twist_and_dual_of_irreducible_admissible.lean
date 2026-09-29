-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_mem_span_exists_rational_torusZeta_twist_and_dual_of_irreducible_admissible
-- name    : LanglandsTunnell.RankinSelberg.forall_mem_span_exists_rational_torusZeta_twist_and_dual_of_irreducible_admissible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/b51098ee-9ac3-5d27-9b63-3bd02b411cf1
-- title:
--   Rationality of twisted torus zeta integrals over ℚₚ
-- statement:
--   Fix a finite place $p$ of $\mathbb{Q}$ (a height-one prime of $\mathcal{O}_{\mathbb{Q}}$), write $F = \mathbb{Q}_p$ for the completion and $q = \#(\mathcal{O}_{\mathbb{Q}}/p)$ for the absolute norm of $p$, and let $\theta_0 : F^\times \to \mathbb{C}^\times$ be a homomorphism. Let $N \neq 0$ be an ideal of $\mathcal{O}_{\mathbb{Q}}$ and let $w_{2} : \mathrm{GL}_2(F) \to \mathbb{C}$ satisfy: the Whittaker transformation law $w_2(u(x)g) = \psi_p(x)\,w_2(g)$ for the standard local additive character $\psi_p$ and upper unipotent $u(x)$; right invariance under the local level-one group at $p$, namely the preimage under the local embedding $\mathrm{GL}_2(F) \to \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}}^{\mathrm{fin}})$ of the finite-adelic level-$N$ subgroup; $w_2 \neq 0$; irreducibility, in the form that every nonzero element $w$ of the $\mathbb{C}$-span $V$ of the right translates $g \mapsto w_2(gh)$ has $w_2$ in the span of the right translates of $w$; admissibility, in the form that for every open subgroup $U \le \mathrm{GL}_2(F)$ there is a finite set $B$ of functions with every right $U$-invariant member of $V$ lying in the span of $B$; and the central character law $w_2(z\cdot g) = \theta_0(z) w_2(g)$ for scalar matrices. Let $w_J \in \mathrm{GL}_2(F)$ have matrix $\begin{pmatrix}0&1\\-1&0\end{pmatrix}$, and let $\eta : F^\times \to \mathbb{C}^\times$ be a locally constant homomorphism. Then, with $F$ carrying its Borel structure, for every $w \in V$ there exist polynomials $P, Q, \tilde P, \tilde Q \in \mathbb{C}[X]$ with $Q \neq 0$ and $\tilde Q \neq 0$, integers $m, \tilde m$ and reals $\sigma_0, \sigma_1$ such that, with $d^\times y$ the pushforward to $F^\times$ of the self-dual additive Haar measure on $F$ restricted to $F \smallsetminus \{0\}$ and multiplied by $|y|^{-1}$, and $|\cdot|$ the module: for all $s$ with $\operatorname{Re} s > \sigma_0$ the function $y \mapsto w(\mathrm{diag}(y,1))\,\eta(y)\,|y|^{s-1/2}$ is integrable and $$\Big(\int_{F^\times} w(\mathrm{diag}(y,1))\eta(y)|y|^{s-1/2}\,d^\times y\Big)\,Q(q^{-s}) = q^{ms}P(q^{-s});$$ and for all $s$ with $\operatorname{Re} s < \sigma_1$ the function $y \mapsto w(\mathrm{diag}(y,1)w_J)\,\eta(y)^{-1}\theta_0(y)^{-1}|y|^{1/2-s}$ is integrable and the corresponding integral times $\tilde Q(q^{-s})$ equals $q^{\tilde m s}\tilde P(q^{-s})$.
--
--   This is the local rationality statement for zeta integrals of Whittaker vectors in an irreducible admissible generic representation of $\mathrm{GL}_2(\mathbb{Q}_p)$, in the form given by Jacquet and Langlands: each twisted torus integral, primal and dual, is a rational function of $q^{-s}$ up to an integral power of $q^{s}$. It feeds the functional equation for these integrals, being cited by [`LanglandsTunnell.RankinSelberg.exists_rational_forall_torusZeta_fe_twist_of_irreducible_admissible`](thm.html#LanglandsTunnell.RankinSelberg.exists_rational_forall_torusZeta_fe_twist_of_irreducible_admissible) within the local analysis supporting the Rankin–Selberg and converse-theorem steps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_forall_mem_span_exists_rational_torusZeta_twist_and_dual_of_irreducible_admissible.lean

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

theorem LanglandsTunnell.RankinSelberg.forall_mem_span_exists_rational_torusZeta_twist_and_dual_of_irreducible_admissible
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
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∃ (P Q Pd Qd : Polynomial ℂ) (m md : ℤ) (σ₀ σ₁ : ℝ), Q ≠ 0 ∧ Qd ≠ 0 ∧
          (∀ s : ℂ, σ₀ < s.re →
            Integrable (fun y : (p.adicCompletion ℚ)ˣ => w (diagOne y) * ((η y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
          (∀ s : ℂ, σ₀ < s.re →
            (∫ y : (p.adicCompletion ℚ)ˣ, w (diagOne y) * ((η y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
          (∀ s : ℂ, s.re < σ₁ →
            Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
              w (diagOne y * wJ) * (((η y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
          (∀ s : ℂ, s.re < σ₁ →
            (∫ y : (p.adicCompletion ℚ)ˣ,
                w (diagOne y * wJ) * (((η y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) * Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) := by sorry
