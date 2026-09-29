-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_rsLocalIntegral22_mul_one_sub_eq_cpow_mul_eval_of_principalSeries2_of_forall_torusZeta_polynomial
-- name    : LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral22_mul_one_sub_eq_cpow_mul_eval_of_principalSeries2_of_forall_torusZeta_polynomial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/44f58155-29ce-5696-aa8a-814affa9dc6e
-- title:
--   Rationality of the local GL₂timesGL₂ Rankin–Selberg integral
-- statement:
--   Fix a non-zero prime $p$ of the ring of integers of $\mathbb{Q}$ and write $F = \mathbb{Q}_p$ for the completion `p.adicCompletion ℚ`, $q =$ `Ideal.absNorm p.asIdeal` for the residue cardinality. The data are as follows.
--
--   *Uniformiser.* A unit $\varpi \in F^\times$ with `Valued.v ϖ = WithZero.exp (-1)`.
--
--   *Inducing characters and chamber.* A pair $\mu = (\mu_0,\mu_1)$ of monoid homomorphisms $F^\times \to \mathbb{C}^\times$, each locally constant (`hμ`), together with real exponents $\sigma_0,\sigma_1$ such that $\lVert \mu_i(a)\rVert = \lVert a\rVert^{\sigma_i}$ for all $a$ (`hσ`) and $\sigma_1 < \sigma_0$ (`h01`).
--
--   *A vector in the principal series.* A function $\varphi : \mathrm{GL}_2(F) \to \mathbb{C}$ lying in `principalSeries2 p μ`, i.e. $\varphi$ is locally constant, satisfies $\varphi(u(x)g) = \varphi(g)$ for every upper unipotent $u(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$ (`upperUnipotent2`), and transforms under the diagonal torus by $\varphi(\mathrm{diag}(a_0,a_1)g) =$ `torusChar2 p μ a` $\cdot$ `halfModulus2 p a` $\cdot \varphi(g)$.
--
--   *Schwartz datum.* A function $\Phi_2 : F \times F \to \mathbb{C}$ which is locally constant and of compact support (`hΦ₂`).
--
--   *Whittaker data on the second factor.* A monoid homomorphism $\theta_0 : F^\times \to \mathbb{C}^\times$, a non-zero ideal $N$ (`hN`), and a function $w_{2,\mathrm{base}} : \mathrm{GL}_2(F) \to \mathbb{C}$ subject to: the Whittaker transformation law $w_{2,\mathrm{base}}\bigl(\begin{pmatrix}1&x\\0&1\end{pmatrix}g\bigr) = \psi_p(x)\, w_{2,\mathrm{base}}(g)$ for the standard local additive character [`NumberField.StandardAddChar.psiLocal ℚ p`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65) (`hw₂law`); right invariance under the local level-one subgroup [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N`](def/AdelicDock_LocalEmbedding.html#L178), the preimage under the local embedding of the finite level-one group of $N$ (`hw₂K`); non-vanishing $w_{2,\mathrm{base}} \neq 0$ (`hw₂ne`); an irreducibility clause (`hw₂irr`): every non-zero $w$ in the $\mathbb{C}$-span $V$ of the right translates $g \mapsto w_{2,\mathrm{base}}(gh)$, $h \in \mathrm{GL}_2(F)$, has $w_{2,\mathrm{base}}$ in the span of its own right translates; an admissibility clause (`hw₂adm`): for every open subgroup $U$ there is a finite set $B$ of functions such that every $w \in V$ which is right $U$-invariant lies in the span of $B$; and the central character law $w_{2,\mathrm{base}}(z\cdot g) = \theta_0(z)\, w_{2,\mathrm{base}}(g)$ for scalar matrices $z \in F^\times$ (`hcentral`).
--
--   *Two Weyl elements.* Elements $w_{0,p}, w_J \in \mathrm{GL}_2(F)$ whose underlying matrices are $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and $\begin{pmatrix}0&1\\-1&0\end{pmatrix}$ respectively.
--
--   *Polynomiality with monomial functional equation for the torus zeta integrals.* Constants $E : \mathrm{Fin}\,2 \to \mathbb{C}$ and $e : \mathrm{Fin}\,2 \to \mathbb{Z}$, and for each $i \in \{0,1\}$ a hypothesis (`hfe0` for $i=0$, `hfe1` for $i=1$) asserting: for every $w \in V$ there exist polynomials $P, P^\vee \in \mathbb{C}[X]$, integers $m, m^\vee$ and reals $\sigma_0', \sigma_1'$ such that, with respect to the multiplicative measure on $F^\times$ obtained by pulling back along `Units.val` the measure `mulMeasure (selfDualHaarAt ℚ p)` (the self-dual additive Haar measure restricted away from $0$ and weighted by $1/\mathrm{modulus}$),
--   (i) for $\mathrm{Re}\,s > \sigma_0'$ the function $y \mapsto w(\mathrm{diag}(y,1))\,\mu_i(y)\,|y|^{\,s-1/2}$ is integrable, and
--   (ii) its integral equals $q^{m s} P(q^{-s})$;
--   (iii) for $\mathrm{Re}\,s < \sigma_1'$ the function $y \mapsto w(\mathrm{diag}(y,1)\,w_J)\,\mu_i(y)^{-1}\theta_0(y)^{-1}|y|^{\,1/2-s}$ is integrable, and
--   (iv) its integral equals $q^{m^\vee s} P^\vee(q^{-s})$;
--   (v) for all $s \in \mathbb{C}$ one has $q^{m^\vee s} P^\vee(q^{-s}) = \bigl(E(i)\, q^{e(i) s}\bigr)\cdot q^{m s} P(q^{-s})$.
--   Here $\mathrm{diag}(y,1)$ is `diagOne y` and $|y| =$ `modulus y` is the local module.
--
--   *Conclusion.* With $\mathrm{GL}_2(F)$ and $F$ carrying their Borel $\sigma$-algebras (`localGLBorel`, `localBorel`): for every Haar measure $\mu_2$ on $\mathrm{GL}_2(F)$, every Haar measure $\mu_{N_2}$ on the range of `unipotentGL2Hom`, i.e. on the upper unipotent subgroup, and every $w_2 \in V$, there exist an integer $m$, a polynomial $P \in \mathbb{C}[X]$ and a real $\sigma_2$ such that for all $s$ with $\mathrm{Re}\,s > \sigma_2$ both of the following hold. First, the function
--   $$g \;\longmapsto\; W'(g)\cdot \bigl(w_2(g)\,\Phi_2(g_{10},g_{11})\bigr)\cdot |\det g|^{\,s+1/2-1/2}, \qquad W'(g) = \int_F \psi_p(x)\,\varphi\bigl(w\,u(x)\,g\bigr)\,d(\mathrm{selfDualHaarAt}\ \mathbb{Q}\ p)(x),$$
--   where $w =$ `antidiagonal2 p` is the antidiagonal matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and $g_{10}, g_{11}$ are the entries of the second row of $g$, is integrable with respect to $\mu_2$ weighted by the density [`HaarQuotient.density`](def/HaarQuotient.html#L25) of the unipotent subgroup relative to $\mu_{N_2}$. Second, the local Rankin–Selberg integral [`RSCarrier.rsLocalIntegral`](def/LanglandsTunnell_RSCarrier.html#L16) formed from these measures, from the modulus $\delta(g) = |\det g|$, at the argument $s+1/2$, with Whittaker function $W'$ and with the second factor $g \mapsto w_2(g)\Phi_2(g_{10},g_{11})$ — that is, the integral of $W'(g)\,w_2(g)\Phi_2(g_{10},g_{11})\,|\det g|^{\,s}$ against the same weighted measure — satisfies
--   $$\Psi(s)\cdot\bigl(1 - \theta_0(\varpi)\,\mu_0(\varpi)\,\mu_1(\varpi)\, q^{-2s}\bigr) \;=\; q^{m s}\,P(q^{-s}).$$
--   Thus the only denominator of $\Psi$ is the central factor attached to $\theta_0\mu_0\mu_1$ at $2s$, and the clearing factor is pinned: no unspecified constant is allowed in it.
--
--   This is the rationality statement for the local $\mathrm{GL}_2\times\mathrm{GL}_2$ Rankin–Selberg (Jacquet) integral with Schwartz data at a finite place: after multiplication by the single Euler factor $1-\theta_0\mu_0\mu_1(\varpi)q^{-2s}$ coming from the centre, the integral becomes a Laurent polynomial in $q^{-s}$. It is used downstream in assembling the cleared functional equation of the Rankin–Selberg product of a principal series with a generic representation, as needed in the converse-theorem input to the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_rsLocalIntegral22_mul_one_sub_eq_cpow_mul_eval_of_principalSeries2_of_forall_torusZeta_polynomial.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral22_mul_one_sub_eq_cpow_mul_eval_of_principalSeries2_of_forall_torusZeta_polynomial
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
            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                ((fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                    φ (antidiagonal2 p * upperUnipotent2 p x * g) ∂(selfDualHaarAt ℚ p)) g * (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  w₂ g * Φ₂ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) ∧
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
