-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_borelEigenfunctional
-- name    : LanglandsTunnell.RankinSelberg.forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_borelEigenfunctional
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/59f8a270-56a5-5e10-800b-74d25a30f3b3
-- title:
--   Cleared Godement–Jacquet functional equation for a Whittaker coefficient
-- statement:
--   Throughout, $p$ is a height-one prime of the ring of integers of $\mathbb{Q}$, $F = \mathbb{Q}_p$ denotes the completion `p.adicCompletion ℚ`, $q =$ `Ideal.absNorm p.asIdeal`, $\psi =$ [`NumberField.StandardAddChar.psiLocal ℚ p`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65) is the standard local additive character of $F$, and $|\cdot| =$ `modulus` is the modulus character of $F$ (the value of the distributive Haar character). For $x \in F$ and $a \in F^\times$, `unipotent x` is the matrix $\begin{pmatrix}1&x\\0&1\end{pmatrix}$, `diagOne a` is $\mathrm{diag}(a,1)$, `Matrix.GeneralLinearGroup.scalar (Fin 2) a` is the scalar matrix $a\cdot 1$, and `transposeInvN (Fin 2) g` is ${}^{t}(g^{-1})$. The measure in $\int \ldots \,\partial(\cdot)$, namely `Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))`, is the multiplicative measure on $F^\times$ obtained from the self-dual additive Haar measure on $F$ by restricting to $F \setminus \{0\}$, multiplying by the density $|x|^{-1}$, and pulling back along $F^\times \to F$.
--
--   The data are: a character $\theta_0 : F^\times \to \mathbb{C}^\times$; a non-zero ideal $N$ of the ring of integers of $\mathbb{Q}$; a function $w_{2,\mathrm{base}} : \mathrm{GL}_2(F) \to \mathbb{C}$; a matrix $w_J \in \mathrm{GL}_2(F)$ with underlying matrix $\begin{pmatrix}0&1\\-1&0\end{pmatrix}$; a locally constant character $\chi : F^\times \to \mathbb{C}^\times$; a constant $E_0 \in \mathbb{C}$ and an integer $e_0$; two further characters $\chi_1, \omega_1 : F^\times \to \mathbb{C}^\times$; and a $\mathbb{C}$-linear functional $\ell_B$ on the space of all functions $\mathrm{GL}_2(F) \to \mathbb{C}$. Write $V$ for the $\mathbb{C}$-span of the right translates $g \mapsto w_{2,\mathrm{base}}(gh)$, $h \in \mathrm{GL}_2(F)$; this subspace occurs literally in every hypothesis below.
--
--   The hypotheses on $w_{2,\mathrm{base}}$ are: `hw₂law`, the Whittaker transformation law $w_{2,\mathrm{base}}(\mathrm{unipotent}\,x \cdot g) = \psi(x)\, w_{2,\mathrm{base}}(g)$ for all $x \in F$, $g \in \mathrm{GL}_2(F)$; `hw₂K`, right invariance $w_{2,\mathrm{base}}(gk) = w_{2,\mathrm{base}}(g)$ for all $k$ in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N`](def/AdelicDock_LocalEmbedding.html#L178), the subgroup of $\mathrm{GL}_2(F)$ obtained by pulling back the finite-adelic level-one subgroup of level $N$ along the local embedding $\mathrm{GL}_2(F) \to \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q},\mathrm{fin}})$; `hw₂ne`, $w_{2,\mathrm{base}} \neq 0$; `hw₂irr`, the irreducibility requirement that every non-zero $w \in V$ has $w_{2,\mathrm{base}}$ in the span of its own right translates; `hw₂adm`, the admissibility requirement that for every open subgroup $U \leq \mathrm{GL}_2(F)$ there is a finite set $B$ of functions on $\mathrm{GL}_2(F)$ whose span contains every $U$-right-invariant element of $V$; and `hcentral`, the central character law $w_{2,\mathrm{base}}(a\cdot 1 \cdot g) = \theta_0(a)\, w_{2,\mathrm{base}}(g)$ for $a \in F^\times$.
--
--   The hypothesis `hfe` (a torus-zeta functional equation with monomial factor $E_0 q^{e_0 s}$) requires that for every $w \in V$ there exist polynomials $P, P_d \in \mathbb{C}[X]$, integers $m, m_d$ and reals $\sigma_0, \sigma_1$ such that: for $\mathrm{Re}\,s > \sigma_0$ the function $y \mapsto w(\mathrm{diag}(y,1))\,\chi(y)\,|y|^{s-1/2}$ is integrable on $F^\times$ for the above multiplicative measure, and its integral equals $q^{ms}P(q^{-s})$; for $\mathrm{Re}\,s < \sigma_1$ the function $y \mapsto w(\mathrm{diag}(y,1)\,w_J)\,\chi(y)^{-1}\theta_0(y)^{-1}|y|^{1/2-s}$ is integrable, and its integral equals $q^{m_d s}P_d(q^{-s})$; and for all $s \in \mathbb{C}$,
--   $$q^{m_d s}P_d(q^{-s}) = \bigl(E_0\, q^{e_0 s}\bigr)\cdot q^{m s}P(q^{-s}).$$
--
--   The hypotheses on $\ell_B$ (a Borel eigenfunctional) are: `hℓB0`, there is $v \in V$ with $\ell_B(v) \neq 0$; `hℓBN`, $\ell_B\bigl(g \mapsto v(g\cdot \mathrm{unipotent}\,x)\bigr) = \ell_B(v)$ for all $x \in F$ and $v \in V$; `hℓBD`, $\ell_B\bigl(g \mapsto v(g\,\mathrm{diag}(a,1))\bigr) = \chi_1(a)\,\ell_B(v)$ for all $a \in F^\times$ and $v \in V$; and `hℓBZ`, $\ell_B\bigl(g \mapsto v(g\cdot a\cdot 1)\bigr) = \omega_1(a)\,\ell_B(v)$ for all $a \in F^\times$ and $v \in V$.
--
--   The conclusion, stated for the Borel $\sigma$-algebras on $F$ and on $\mathrm{GL}_2(F)$, asserts the following for every Haar measure $\mu_2$ on $\mathrm{GL}_2(F)$, every $w \in V$, every locally constant compactly supported $\Phi : M_2(F) \to \mathbb{C}$, all polynomials $P, P_d, Q, Q_d \in \mathbb{C}[X]$ with $Q \neq 0$ and $Q_d \neq 0$, all integers $m, m_d$ and all reals $\sigma_2, \sigma_3$. Assume the four clauses:
--
--   (i) for $\mathrm{Re}\,s > \sigma_2$ the function $g \mapsto w(g)\,\Phi(g)\,\chi(\det g)\,|\det g|^{s+1/2}$ is $\mu_2$-integrable;
--
--   (ii) for $\mathrm{Re}\,s > \sigma_2$, `godementZeta2 p μ₂ w Φ χ (s + 1/2)`, that is $\int_{\mathrm{GL}_2(F)} w(g)\Phi(g)\chi(\det g)|\det g|^{s+1/2}\,d\mu_2(g)$, multiplied by $Q(q^{-s})$, equals $q^{ms}P(q^{-s})$;
--
--   (iii) for $\mathrm{Re}\,s > \sigma_3$ the function $g \mapsto w({}^{t}g^{-1})\cdot \widehat{\Phi}(g)\cdot \chi^{-1}(\det g)\,|\det g|^{s+3/2}$ is $\mu_2$-integrable, where $\widehat{\Phi} =$ `matFourier22 p ψ Φ` is the iterated column-wise Fourier transform of $\Phi$ with respect to $\psi$ and the self-dual measure;
--
--   (iv) for $\mathrm{Re}\,s > \sigma_3$, the Godement zeta integral of the coefficient $g \mapsto w({}^{t}g^{-1})$ against $\widehat{\Phi}$ and $\chi^{-1}$ at $s + 3/2$, multiplied by $Q_d(q^{-s})$, equals $q^{m_d s}P_d(q^{-s})$.
--
--   Then for all $s \in \mathbb{C}$ the cleared functional equation holds:
--   $$1\cdot\bigl(q^{m_d s}P_d(q^{-s})\bigr)\cdot Q(q^{s}) = \bigl(E_0\, q^{-e_0 s}\bigr)\cdot\bigl(q^{-m s}P(q^{s})\bigr)\cdot Q_d(q^{-s}),$$
--   where the factors $1$ and $E_0$ appear as the values at $q^{s}$ of the constant polynomials $1$ and $\mathrm{C}(E_0)$, the exponent $-e_0 s$ as $((-e_0 : \mathbb{Z}) : \mathbb{C})\cdot s$ and the exponent $-ms$ as $m\cdot(-s)$. Note that the two sides are products of the numerator data of (ii) and (iv) with the denominators swapped and the variable $q^{-s}$ replaced by $q^{s}$ in three of the four evaluations; no integrability or convergence statement is part of the conclusion.
--
--   This is the local Godement–Jacquet functional equation on $\mathrm{GL}_2$ over $\mathbb{Q}_p$ for a zeta integral whose matrix coefficient is a Whittaker function, in the case where the representation carries a non-zero Borel eigenfunctional, so that it is realised inside a principal series and the zeta integral unfolds into abelian Tate integrals. It feeds the unconditional form `forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe` and the principal-series Rankin–Selberg statement `forall_rsLocalIntegral22_schwartz_centralCleared_laurentFE_of_principalSeries2_of_forall_torusZeta_fe_of_borelEigenfunctional`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_borelEigenfunctional.lean

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

theorem LanglandsTunnell.RankinSelberg.forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_borelEigenfunctional
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

    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)

    (E₀ : ℂ) (e₀ : ℤ)
    (hfe : letI := localBorel ℚ p
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₀ σ₁ : ℝ),
        (∀ s : ℂ, σ₀ < s.re →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, σ₀ < s.re →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y * wJ) * (((χ y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
              ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y * wJ) * (((χ y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ,
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            (E₀ * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e₀ : ℂ) * s)) *
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))))

    (χ₁ ω₁ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (ℓB : (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) →ₗ[ℂ] ℂ)
    (hℓB0 : ∃ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ℓB v ≠ 0)
    (hℓBN : ∀ (x : (p.adicCompletion ℚ)), ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ℓB (fun g : GL (Fin 2) (p.adicCompletion ℚ) => v (g * unipotent x)) = ℓB v)
    (hℓBD : ∀ (a : (p.adicCompletion ℚ)ˣ), ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ℓB (fun g : GL (Fin 2) (p.adicCompletion ℚ) => v (g * diagOne a)) = ((χ₁ a : ℂˣ) : ℂ) * ℓB v)
    (hℓBZ : ∀ (a : (p.adicCompletion ℚ)ˣ), ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ℓB (fun g : GL (Fin 2) (p.adicCompletion ℚ) => v (g * Matrix.GeneralLinearGroup.scalar (Fin 2) a)) = ((ω₁ a : ℂˣ) : ℂ) * ℓB v)
    :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∀ (Φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ), IsLocallyConstant Φ → HasCompactSupport Φ →
          ∀ (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ), Q ≠ 0 → Qd ≠ 0 →

            (∀ s : ℂ, σ₂ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                w g * Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2)) μ₂) →

            (∀ s : ℂ, σ₂ < s.re →
              godementZeta2 p μ₂ w Φ χ (s + 1 / 2) * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) →

            (∀ s : ℂ, σ₃ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                w (transposeInvN (Fin 2) g) *
                  matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
                  ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 3 / 2)) μ₂) →

            (∀ s : ℂ, σ₃ < s.re →
              godementZeta2 p μ₂ (fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (transposeInvN (Fin 2) g))
                  (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ) χ⁻¹ (s + 3 / 2) * Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) →

            (∀ s : ℂ,
              ((1 : Polynomial ℂ)).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) *
                  ((Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) *
                  Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) =
                ((Polynomial.C E₀).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) * (Ideal.absNorm p.asIdeal : ℂ) ^ (((-e₀ : ℤ) : ℂ) * s)) *
                  ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s)) *
                  Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) := by sorry
