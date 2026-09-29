-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral22_schwartz_centralCleared_laurentFE_of_principalSeries2_of_forall_torusZeta_fe
-- name    : LanglandsTunnell.RankinSelberg.forall_rsLocalIntegral22_schwartz_centralCleared_laurentFE_of_principalSeries2_of_forall_torusZeta_fe
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/bc057170-613f-5ede-8446-28ea39a34d8b
-- title:
--   Local GL₂× GL₂ functional equation for Laurent numerators
-- statement:
--   Fix a height-one prime $p$ of $\mathcal O_{\mathbb Q}$, and write $F =$ `p.adicCompletion ℚ` for the completion, $\mathcal O_F$ for its valuation subring and $N_p =$ `Ideal.absNorm p.asIdeal` for the residue cardinality. All measure-theoretic structures are the Borel ones: the $\sigma$-algebra `localBorel ℚ p` on $F$, and `localGLBorel ℚ p` together with its `BorelSpace` instance on $GL_2(F)$.
--
--   The data are as follows.
--
--   *Uniformiser.* An element $\varpi \in \mathcal O_F$ whose image in $F$ is nonzero (`hπ`) and has valuation $\exp(-1)$ (`hϖ`); `Units.mk0` turns this image into a unit of $F$.
--
--   *Inducing characters.* A pair $\mu = (\mu_0,\mu_1)$ of monoid homomorphisms $F^\times \to \mathbb C^\times$, each locally constant (`hμ`), and real exponents $\sigma_0,\sigma_1$ with $\|\mu_i(a)\| = \|a\|^{\sigma_i}$ for all $a \in F^\times$ (`hσ`), lying in the chamber $\sigma_1 < \sigma_0$ (`h01`).
--
--   *Principal series vector.* A function $\varphi : GL_2(F) \to \mathbb C$ with `hφ` asserting $\varphi \in$ `principalSeries2 p μ`, i.e. $\varphi$ is locally constant, $\varphi(\mathrm{upperUnipotent2}\,x \cdot g) = \varphi(g)$ for all $x \in F$, and $\varphi(\mathrm{diagonal2}\,a \cdot g) = \mathrm{torusChar2}\,\mu\,a \cdot \mathrm{halfModulus2}\,a \cdot \varphi(g)$ for all $a : \mathrm{Fin}\,2 \to F^\times$.
--
--   *Schwartz–Bruhat function.* A function $\Phi_2 : F \times F \to \mathbb C$ which is locally constant and compactly supported (`hΦ₂`).
--
--   *Generic vector.* A monoid homomorphism $\theta_0 : F^\times \to \mathbb C^\times$, a nonzero ideal $N$ of $\mathcal O_{\mathbb Q}$ (`hN`), and a function $w_{2,\mathrm{base}} : GL_2(F) \to \mathbb C$ subject to five conditions: `hw₂law`, $w_{2,\mathrm{base}}(\mathrm{unipotent}\,x \cdot g) = \psi_p(x)\, w_{2,\mathrm{base}}(g)$ for the standard local additive character `psiLocal ℚ p`; `hw₂K`, right invariance under the subgroup [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N`](def/AdelicDock_LocalEmbedding.html#L178), the pullback along the local embedding of the finite-adelic level-one subgroup of $N$; `hw₂ne`, $w_{2,\mathrm{base}} \neq 0$; `hw₂irr`, an irreducibility clause: every nonzero $w$ in the $\mathbb C$-span of the right translates $g \mapsto w_{2,\mathrm{base}}(gh)$ has $w_{2,\mathrm{base}}$ in the span of its own right translates; `hw₂adm`, an admissibility clause: for every open subgroup $U \le GL_2(F)$ there is a finite set $B$ of functions such that every $U$-right-invariant element of the span of the right translates of $w_{2,\mathrm{base}}$ lies in the span of $B$. Finally `hcentral` records the central character: $w_{2,\mathrm{base}}(\mathrm{scalar}(z)\,g) = \theta_0(z)\, w_{2,\mathrm{base}}(g)$.
--
--   *Weyl elements.* Elements $w_{0,p}, w_J \in GL_2(F)$ with underlying matrices $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ (`hw₀p`) and $\begin{pmatrix}0&1\\-1&0\end{pmatrix}$ (`hwJ`).
--
--   *Torus zeta functional equations.* Constants $E : \mathrm{Fin}\,2 \to \mathbb C$ and exponents $e : \mathrm{Fin}\,2 \to \mathbb Z$, and two hypotheses `hfe0`, `hfe1` of identical shape, for $i = 0$ and $i = 1$ respectively: for every $w$ in the span of the right translates of $w_{2,\mathrm{base}}$ there exist polynomials $P, P^\vee \in \mathbb C[X]$, integers $m, m^\vee$ and reals $\sigma_0', \sigma_1'$ such that, with respect to the multiplicative measure on $F^\times$ obtained by pulling back along `Units.val` the measure `mulMeasure (selfDualHaarAt ℚ p)` (the self-dual additive Haar measure at $p$ restricted to $F \setminus \{0\}$ with density $\mathrm{modulus}^{-1}$): (i) for $\mathrm{Re}\,s > \sigma_0'$ the function $y \mapsto w(\mathrm{diagOne}\,y)\,\mu_i(y)\,\mathrm{modulus}(y)^{s-1/2}$ is integrable, where $\mathrm{diagOne}\,y$ is the diagonal matrix with entries $y, 1$; (ii) for $\mathrm{Re}\,s > \sigma_0'$ its integral equals $N_p^{ms}P(N_p^{-s})$; (iii) for $\mathrm{Re}\,s < \sigma_1'$ the function $y \mapsto w(\mathrm{diagOne}\,y \cdot w_J)\,\mu_i(y)^{-1}\theta_0(y)^{-1}\mathrm{modulus}(y)^{1/2-s}$ is integrable; (iv) for $\mathrm{Re}\,s < \sigma_1'$ its integral equals $N_p^{m^\vee s}P^\vee(N_p^{-s})$; and (v) for all $s \in \mathbb C$, $N_p^{m^\vee s}P^\vee(N_p^{-s}) = \bigl(E_i\,N_p^{e_i s}\bigr)\cdot N_p^{ms}P(N_p^{-s})$.
--
--   Under these hypotheses the assertion is the following. Let $\mu_2$ be a Haar measure on $GL_2(F)$ and $\mu_{N_2}$ a Haar measure on the range of `unipotentGL2Hom`, the homomorphism from the multiplicative copy of the additive group $F$ sending $x$ to the upper unipotent matrix `unipotentGL2 x`. Let $w_2$ belong to the span of the right translates of $w_{2,\mathrm{base}}$, let $P_1, P_2 \in \mathbb C[X]$, $m_1, m_2 \in \mathbb Z$ and $\sigma_4, \sigma_5 \in \mathbb R$. Write $c = \theta_0(\varpi)\mu_0(\varpi)\mu_1(\varpi)$ for the value at the uniformiser, $\delta(g) = \mathrm{modulus}(\det g)$, and recall that [`RSCarrier.rsLocalIntegral`](def/LanglandsTunnell_RSCarrier.html#L16) $\mu_2\,H\,\mu_{N_2}\,\delta\,s\,W\,F$ is the integral of $W(g)F(g)\delta(g)^{s-1/2}$ against $\mu_2$ with density [`HaarQuotient.density H μ_{N_2}`](def/HaarQuotient.html#L25), taken here with $H$ the above unipotent subgroup and at the argument $s + 1/2$.
--
--   Assume first (primal Laurent form) that for all $s$ with $\mathrm{Re}\,s > \sigma_4$,
--   $$\mathrm{rsLocalIntegral}\bigl(\delta, s+\tfrac12, W', F_1\bigr)\cdot\bigl(1 - c\,N_p^{-2s}\bigr) = N_p^{m_1 s}P_1(N_p^{-s}),$$
--   where $W'(g) = \int_F \psi_p(x)\,\varphi(\mathrm{antidiagonal2}\cdot \mathrm{upperUnipotent2}\,x \cdot g)\,dx$ against `selfDualHaarAt ℚ p`, and $F_1(g) = w_2(g)\,\Phi_2(g_{10}, g_{11})$ is evaluated on the bottom row of $g$.
--
--   Assume second (dual Laurent form) that for all $s$ with $\mathrm{Re}\,s > \sigma_5$,
--   $$\mathrm{rsLocalIntegral}\bigl(\delta, s+\tfrac12, \widetilde W', \widetilde F\bigr)\cdot\bigl(1 - c^{-1}N_p^{-2}N_p^{-2s}\bigr) = N_p^{m_2 s}P_2(N_p^{-s}),$$
--   where $\widetilde W'(g) = \int_F \psi_p(x)\,\varphi(\mathrm{antidiagonal2}\cdot\mathrm{upperUnipotent2}\,x\cdot(w_{0,p}\cdot \mathrm{transposeInvN}\,g))\,dx$, with $\mathrm{transposeInvN}\,g$ the transpose of $g^{-1}$, and
--   $$\widetilde F(g) = \delta(g)\, w_2(w_{0,p}\cdot\mathrm{transposeInvN}\,g)\int_{F\times F}\Phi_2(u)\,\psi_p\bigl(u_1 g_{10} + u_2 g_{11}\bigr)\,du,$$
--   the last integral being against the product of `selfDualHaarAt ℚ p` with itself, i.e. the Fourier transform of $\Phi_2$ evaluated at the bottom row of $g$.
--
--   The conclusion is the identity of functions of $s$, valid for every $s \in \mathbb C$:
--   $$N_p^{m_2 s}P_2(N_p^{-s})\cdot\bigl(1 - c\,N_p^{2s}\bigr) = \Bigl(\mu_0(-1)\mu_1(-1)\,E_0E_1\,N_p^{-(e_0+e_1)s}\Bigr)\cdot\Bigl(N_p^{m_1(-s)}P_1(N_p^{s})\Bigr)\cdot\bigl(1 - c^{-1}N_p^{-2}N_p^{-2s}\bigr).$$
--   No integrability or convergence is asserted in the conclusion: it is an identity between the two centre-cleared Laurent numerators, holding on all of $\mathbb C$.
--
--   This is the local Rankin–Selberg functional equation at $p$ relating the $GL_2\times GL_2$ zeta integral of a chamber principal series against a generic admissible vector to its dual integral, expressed on the two numerators obtained after clearing the central Tate factors $(1-cN_p^{-2s})$ and $(1-c^{-1}N_p^{-2-2s})$. It is proved by splitting according to the dichotomy of `kirillov_vanish_near_zero_or_exists_borelEigenfunctional_of_irreducible_admissible` and invoking the cuspidal and Borel-eigenfunctional cases separately, and it feeds the cleared functional equation `forall_rsLocalIntegral22_schwartz_clearedFE_of_principalSeries2_of_forall_torusZeta_fe_ed2` used in the converse-theorem input to the Langlands–Tunnell step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral22_schwartz_centralCleared_laurentFE_of_principalSeries2_of_forall_torusZeta_fe.lean

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

theorem LanglandsTunnell.RankinSelberg.forall_rsLocalIntegral22_schwartz_centralCleared_laurentFE_of_principalSeries2_of_forall_torusZeta_fe
    (p : HeightOneSpectrum (𝓞 ℚ))

    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))

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
          ∀ (P₁ P₂ : Polynomial ℂ) (m₁ m₂ : ℤ) (σ₄ σ₅ : ℝ),

            (∀ s : ℂ, σ₄ < s.re →
              RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                (s + 1 / 2)
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                    φ (antidiagonal2 p * upperUnipotent2 p x * g) ∂(selfDualHaarAt ℚ p))
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  w₂ g * Φ₂ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)) *
                (1 - (((θ₀ (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) * ((μ 0 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) * ((μ 1 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(2 : ℂ) * s)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((m₁ : ℂ) * s) * P₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) →

            (∀ s : ℂ, σ₅ < s.re →
              RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                (s + 1 / 2)
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                    φ (antidiagonal2 p * upperUnipotent2 p x * (w₀p * transposeInvN (Fin 2) g)) ∂(selfDualHaarAt ℚ p))
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g) *
                    (∫ u : p.adicCompletion ℚ × p.adicCompletion ℚ, Φ₂ u *
                      NumberField.StandardAddChar.psiLocal ℚ p
                        (u.1 * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 + u.2 * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)
                    ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)))) *
                (1 - ((((θ₀ (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) * ((μ 0 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) * ((μ 1 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)))⁻¹ * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(2 : ℂ)) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(2 : ℂ) * s)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((m₂ : ℂ) * s) * P₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) →

            ∀ s : ℂ,
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((m₂ : ℂ) * s) * P₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (1 - (((θ₀ (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) * ((μ 0 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) * ((μ 1 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((2 : ℂ) * s)) =
                ((((μ 0 (-1) : ℂˣ) : ℂ) * ((μ 1 (-1) : ℂˣ) : ℂ)) * (E 0 * E 1) * (Ideal.absNorm p.asIdeal : ℂ) ^ (((-(e 0 + e 1) : ℤ) : ℂ) * s)) *
                  ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m₁ : ℂ) * (-s)) * P₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s)) *
                  (1 - ((((θ₀ (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) * ((μ 0 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) * ((μ 1 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)))⁻¹ * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(2 : ℂ)) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(2 : ℂ) * s)) := by sorry
