-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_rsLocalIntegral22_mul_one_sub_eq_cpow_mul_eval_of_principalSeries2_of_forall_torusZeta_polynomial_core
-- name    : LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral22_mul_one_sub_eq_cpow_mul_eval_of_principalSeries2_of_forall_torusZeta_polynomial_core
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/36760957-419d-5f07-8750-0c00df6b3125
-- title:
--   Rationality of the local (2,2) Rankin–Selberg integral
-- statement:
--   Fix a height one prime $p$ of $\mathcal O_{\mathbb Q}$, write $F = \mathbb Q_p$ for the completion `p.adicCompletion ℚ`, and let $q =$ `Ideal.absNorm p.asIdeal` be the absolute norm of $p$.
--
--   The data are: a unit $\varpi \in F^\times$ normalised by `hϖ` so that $v(\varpi) = \exp(-1)$, i.e. a uniformiser; a pair $\mu = (\mu_0,\mu_1)$ of multiplicative characters $F^\times \to \mathbb C^\times$; exponents $\sigma : \mathrm{Fin}\,2 \to \mathbb R$; a function $\varphi$ on $\mathrm{GL}_2(F)$; a function $\Phi_2$ on $F \times F$; a further character $\theta_0 : F^\times \to \mathbb C^\times$; a nonzero ideal $N$ of $\mathcal O_{\mathbb Q}$ (`hN`); a function $w_{2\mathrm{base}}$ on $\mathrm{GL}_2(F)$; two elements $w_{0p}, w_J \in \mathrm{GL}_2(F)$ whose underlying matrices are prescribed by `hw₀p` to be $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and by `hwJ` to be $\begin{pmatrix}0&1\\-1&0\end{pmatrix}$; and constants $E : \mathrm{Fin}\,2 \to \mathbb C$, $e : \mathrm{Fin}\,2 \to \mathbb Z$.
--
--   *Character hypotheses.* `hμ` asserts that each $\mu_i$ is locally constant; `hσ` that $\|\mu_i(a)\| = \|a\|^{\sigma i}$ for all $a \in F^\times$; and `h01` that $\sigma 1 < \sigma 0$ (the chamber condition).
--
--   *Principal series hypothesis.* `hφ` asserts $\varphi \in$ `principalSeries2 p μ`, that is: $\varphi$ is locally constant, invariant under left translation by the upper unipotent matrices $\begin{pmatrix}1&x\\0&1\end{pmatrix}$, and satisfies $\varphi(\mathrm{diag}(a_0,a_1)g) = \chi_\mu(a)\,\delta^{1/2}(a)\,\varphi(g)$ with the torus character and half-modulus factors of that definition.
--
--   *Schwartz hypothesis.* `hΦ₂` asserts that $\Phi_2$ is locally constant with compact support.
--
--   *Hypotheses on $w_{2\mathrm{base}}$ (a Whittaker-type vector).* `hw₂law`: $w_{2\mathrm{base}}(u(x)g) = \psi_p(x)\,w_{2\mathrm{base}}(g)$ for all $x \in F$, where $u(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$ and $\psi_p$ is the standard local additive character [`NumberField.StandardAddChar.psiLocal ℚ p`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65). `hw₂K`: $w_{2\mathrm{base}}$ is invariant under right translation by every $k$ in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N`](def/AdelicDock_LocalEmbedding.html#L178), the pullback along the local embedding $\mathrm{GL}_2(F) \to \mathrm{GL}_2(\mathbb A_{\mathbb Q,\mathrm{fin}})$ of the finite level-one subgroup of level $N$. `hw₂ne`: $w_{2\mathrm{base}} \neq 0$. `hw₂irr`: every nonzero $w$ in the $\mathbb C$-span $V$ of the right translates $g \mapsto w_{2\mathrm{base}}(gh)$ has $w_{2\mathrm{base}}$ in the span of the right translates of $w$ (irreducibility of $V$). `hw₂adm`: for every open subgroup $U \le \mathrm{GL}_2(F)$ there is a finite set $B$ of functions such that every $w \in V$ invariant under right translation by $U$ lies in the span of $B$ (admissibility). `hcentral`: $w_{2\mathrm{base}}(z I_2 \cdot g) = \theta_0(z)\,w_{2\mathrm{base}}(g)$, so $\theta_0$ is the central character.
--
--   *Torus zeta hypotheses `hfe0` and `hfe1`.* For $i = 0$ and $i = 1$ respectively, these assert that for every $w \in V$ there exist polynomials $P, P^\vee \in \mathbb C[X]$, integers $m, m^\vee$, and reals $\sigma_0, \sigma_1$ such that, with the multiplicative measure on $F^\times$ obtained by pulling back along `Units.val` the measure `mulMeasure (selfDualHaarAt ℚ p)` (the self-dual additive Haar measure restricted to $F \setminus \{0\}$ with density $\mathrm{mod}(x)^{-1}$): (i) for $\mathrm{Re}\,s > \sigma_0$ the function $y \mapsto w(\mathrm{diag}(y,1))\,\mu_i(y)\,\mathrm{mod}(y)^{s-1/2}$ is integrable, and (ii) its integral equals $q^{ms}P(q^{-s})$; (iii) for $\mathrm{Re}\,s < \sigma_1$ the function $y \mapsto w(\mathrm{diag}(y,1)w_J)\,\mu_i(y)^{-1}\theta_0(y)^{-1}\mathrm{mod}(y)^{1/2-s}$ is integrable, and (iv) its integral equals $q^{m^\vee s}P^\vee(q^{-s})$; and (v) for all $s \in \mathbb C$ the monomial functional equation $q^{m^\vee s}P^\vee(q^{-s}) = \bigl(E_i\,q^{(e_i)s}\bigr)\cdot q^{ms}P(q^{-s})$ holds. Here $\mathrm{diag}(y,1)$ is `diagOne y` and $\mathrm{mod}$ is the module `modulus` given by the distributive Haar character.
--
--   *Conclusion.* With $\mathrm{GL}_2(F)$ and $F$ carrying their Borel $\sigma$-algebras: for every Haar measure $\mu_2$ on $\mathrm{GL}_2(F)$, every Haar measure $\mu_{N_2}$ on the range of `unipotentGL2Hom` (the unipotent subgroup $\{u(x)\}$), and every $w_2 \in V$, there exist an integer $m$, a polynomial $P \in \mathbb C[X]$ and a real $\sigma_2$ such that for all $s$ with $\mathrm{Re}\,s > \sigma_2$,
--   $$\Psi(s)\cdot\bigl(1 - \theta_0(\varpi)\mu_0(\varpi)\mu_1(\varpi)\,q^{-2s}\bigr) = q^{ms}\,P(q^{-s}),$$
--   where $\Psi(s)$ is the value [`RSCarrier.rsLocalIntegral`](def/LanglandsTunnell_RSCarrier.html#L16) at the arguments $\mu_2$, the unipotent subgroup with $\mu_{N_2}$, the modulus function $g \mapsto \mathrm{mod}(\det g)$, the complex parameter $s + 1/2$, the Whittaker function
--   $$W(g) = \int_F \psi_p(x)\,\varphi\bigl(w_0\,u(x)\,g\bigr)\,d\,(\mathrm{selfDualHaarAt}\ \mathbb Q\ p)$$
--   (the Jacquet integral, $w_0 =$ `antidiagonal2 p` and $u(x) =$ `upperUnipotent2 p x`), and the function $g \mapsto w_2(g)\,\Phi_2(g_{10},g_{11})$ built from the second row of $g$; by the definition of `rsLocalIntegral` this value is
--   $$\int_{\mathrm{GL}_2(F)} W(g)\,w_2(g)\,\Phi_2(g_{10},g_{11})\,\mathrm{mod}(\det g)^{s}\;d\bigl(\mu_2\text{ with density }\mathrm{HaarQuotient.density}\bigr),$$
--   the shift $s + 1/2$ in the parameter producing the exponent $s$ on $\mathrm{mod}(\det g)$.
--
--   This is the rationality statement for the local Rankin–Selberg integral of a principal series Whittaker function against a vector in a generic irreducible admissible representation with central character $\theta_0$, twisted by a locally constant compactly supported function on the second row: after multiplication by the Euler factor $1 - \theta_0\mu_0\mu_1(\varpi)q^{-2s}$ coming from the centre, the integral becomes a Laurent polynomial in $q^{-s}$, so the only pole can come from that factor. It feeds the companion result `exists_rsLocalIntegral22_mul_one_sub_eq_cpow_mul_eval_of_principalSeries2_of_forall_torusZeta_polynomial`, part of the local theory supporting the converse theorem used in the Langlands–Tunnell step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_rsLocalIntegral22_mul_one_sub_eq_cpow_mul_eval_of_principalSeries2_of_forall_torusZeta_polynomial_core.lean

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

open IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open AutomorphicForm
open LanglandsTunnell.RankinSelberg

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

theorem LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral22_mul_one_sub_eq_cpow_mul_eval_of_principalSeries2_of_forall_torusZeta_polynomial_core
    (p : HeightOneSpectrum (𝓞 ℚ))

    (ϖ : (p.adicCompletion ℚ)ˣ) (hϖ : Valued.v (ϖ : p.adicCompletion ℚ) = WithZero.exp (-1 : ℤ))

    (μ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hμ : ∀ i, IsLocallyConstant (μ i))
    (σ : Fin 2 → ℝ)
    (hσ : ∀ (i : Fin 2) (a : (p.adicCompletion ℚ)ˣ), ‖((μ i a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (σ i))
    (h01 : σ 1 < σ 0)
    (φ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ : φ ∈ principalSeries2 p μ)

    (Φ₂ : p.adicCompletion ℚ × p.adicCompletion ℚ → ℂ) (hΦ₂ : IsLocallyConstant Φ₂ ∧ HasCompactSupport Φ₂)

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
    (wJ : GL (Fin 2) (p.adicCompletion ℚ)) (hwJ : (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; -1, 0])

    (E : Fin 2 → ℂ) (e : Fin 2 → ℤ)
    (hfe0 : letI := localBorel ℚ p
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₀ σ₁ : ℝ),
        (∀ s : ℂ, σ₀ < s.re →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y) * ((μ 0 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, σ₀ < s.re →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((μ 0 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y * wJ) * (((μ 0 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
              ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y * wJ) * (((μ 0 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ,
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            (E 0 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e 0 : ℂ) * s)) *
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))))
    (hfe1 : letI := localBorel ℚ p
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₀ σ₁ : ℝ),
        (∀ s : ℂ, σ₀ < s.re →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y) * ((μ 1 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, σ₀ < s.re →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((μ 1 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y * wJ) * (((μ 1 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
              ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y * wJ) * (((μ 1 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ,
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            (E 1 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e 1 : ℂ) * s)) *
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))))
    :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
          (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
        ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          ∃ (m : ℤ) (P : Polynomial ℂ) (σ₂ : ℝ), ∀ s : ℂ, σ₂ < s.re →
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                (s + 1 / 2)
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                    φ (antidiagonal2 p * upperUnipotent2 p x * g) ∂(selfDualHaarAt ℚ p))
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  w₂ g * Φ₂ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)) *
                (1 - ((θ₀ ϖ : ℂˣ) : ℂ) * ((μ 0 ϖ : ℂˣ) : ℂ) * ((μ 1 ϖ : ℂˣ) : ℂ) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(2 : ℂ) * s)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) := by sorry
