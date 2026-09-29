-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral22_schwartz_centralCleared_laurentFE_of_principalSeries2_of_forall_torusZeta_fe_of_borelEigenfunctional
-- name    : LanglandsTunnell.RankinSelberg.forall_rsLocalIntegral22_schwartz_centralCleared_laurentFE_of_principalSeries2_of_forall_torusZeta_fe_of_borelEigenfunctional
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/ee68aace-b527-5b1c-abdf-f5e44f6aad56
-- title:
--   Centre-cleared local GL₂× GL₂ functional equation, principal-series branch
-- statement:
--   Throughout, $p$ is a maximal ideal of $\mathcal{O}_{\mathbb{Q}}$, $K_p =$ `p.adicCompletion ℚ` its completion, $q =$ `Ideal.absNorm p.asIdeal` the residue cardinality, $\psi_p =$ [`NumberField.StandardAddChar.psiLocal ℚ p`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65) the standard local additive character, $|\cdot| =$ `modulus` the module of $K_p$ (defined through `distribHaarChar`, and $0$ at $0$), $dx$ the self-dual additive Haar measure `selfDualHaarAt ℚ p`, and $d^{*}y$ the measure on $K_p^{\times}$ obtained by pulling back along `Units.val` the measure `mulMeasure (selfDualHaarAt ℚ p)`, i.e. $dx$ restricted to $K_p\setminus\{0\}$ with density $|x|^{-1}$. For a unit $y$, `diagOne y` denotes $\mathrm{diag}(y,1) \in GL_2(K_p)$, `unipotent x` and `upperUnipotent2 p x` the matrix $\begin{pmatrix}1&x\\0&1\end{pmatrix}$, `antidiagonal2 p` the matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$, and `transposeInvN (Fin 2) g` the transpose of $g^{-1}$.
--
--   The data are as follows. A uniformiser: an element $\varpi$ of the valuation ring of $K_p$ whose image in $K_p$ is non-zero (`hπ`) and has valuation $\exp(-1)$ (`hϖ`). A pair of inducing characters: $\mu_0,\mu_1 : K_p^{\times} \to \mathbb{C}^{\times}$, locally constant (`hμ`), together with real exponents $\sigma_0,\sigma_1$ such that $\|\mu_i(a)\| = \|a\|^{\sigma_i}$ for all units $a$ (`hσ`), subject to the chamber condition $\sigma_1 < \sigma_0$ (`h01`). A section of the induced representation: $\varphi : GL_2(K_p) \to \mathbb{C}$ lying in `principalSeries2 p μ`, i.e. $\varphi$ is locally constant, left invariant under upper unipotent matrices, and satisfies $\varphi(\mathrm{diag}(a_0,a_1)g) = (\mathrm{torusChar2}\ \mu)(a)\,(\mathrm{halfModulus2})(a)\,\varphi(g)$ for diagonal matrices. A Schwartz–Bruhat function: $\Phi_2 : K_p \times K_p \to \mathbb{C}$, locally constant with compact support (`hΦ₂`).
--
--   The second factor is given by a Whittaker vector $w_{2,\mathrm{base}} : GL_2(K_p) \to \mathbb{C}$, and throughout $V$ denotes the $\mathbb{C}$-span of the right translates $g \mapsto w_{2,\mathrm{base}}(gh)$, $h \in GL_2(K_p)$. The hypotheses on it are: the Whittaker transformation law $w_{2,\mathrm{base}}(n(x)g) = \psi_p(x)\,w_{2,\mathrm{base}}(g)$ (`hw₂law`); right invariance under the local level subgroup [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N`](def/AdelicDock_LocalEmbedding.html#L178) attached to a non-zero ideal $N$ of $\mathcal{O}_{\mathbb{Q}}$ (`hN`, `hw₂K`); non-vanishing $w_{2,\mathrm{base}} \ne 0$ (`hw₂ne`); irreducibility in the form that every non-zero $w \in V$ has $w_{2,\mathrm{base}}$ in the span of the right translates of $w$ (`hw₂irr`); admissibility in the form that for every open subgroup $U$ there is a finite set $B$ of functions such that every $U$-right-invariant element of $V$ lies in the span of $B$ (`hw₂adm`); and a central character: $w_{2,\mathrm{base}}(z\cdot 1_2\, g) = \theta_0(z)\,w_{2,\mathrm{base}}(g)$ for a character $\theta_0 : K_p^{\times} \to \mathbb{C}^{\times}$ (`hcentral`). Two Weyl-type elements are fixed: $w_{0,p}$ with matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and $w_J$ with matrix $\begin{pmatrix}0&1\\-1&0\end{pmatrix}$.
--
--   Monomial torus functional equations are assumed with constants $E : \mathrm{Fin}\,2 \to \mathbb{C}$ and $e : \mathrm{Fin}\,2 \to \mathbb{Z}$: for $i = 0$ (`hfe0`) and $i = 1$ (`hfe1`), every $w \in V$ admits polynomials $P, P^{d} \in \mathbb{C}[X]$, integers $m, m^{d}$ and reals $\sigma_0', \sigma_1'$ such that (five clauses) the primal torus integrand $y \mapsto w(\mathrm{diag}(y,1))\,\mu_i(y)\,|y|^{s-1/2}$ is $d^{*}y$-integrable for $\operatorname{Re} s > \sigma_0'$ and its integral equals $q^{m s}P(q^{-s})$ there; the dual torus integrand $y \mapsto w(\mathrm{diag}(y,1)\,w_J)\,\mu_i(y)^{-1}\theta_0(y)^{-1}|y|^{1/2-s}$ is $d^{*}y$-integrable for $\operatorname{Re} s < \sigma_1'$ and its integral equals $q^{m^{d}s}P^{d}(q^{-s})$ there; and, as an identity of functions of $s \in \mathbb{C}$, $q^{m^{d}s}P^{d}(q^{-s}) = \bigl(E_i\,q^{e_i s}\bigr)\,q^{m s}P(q^{-s})$.
--
--   Finally, the principal-series branch hypothesis: there are characters $\chi_1, \omega_1 : K_p^{\times} \to \mathbb{C}^{\times}$ and a $\mathbb{C}$-linear functional $\ell_B$ on the space of functions $GL_2(K_p) \to \mathbb{C}$ which is non-zero on $V$ (`hℓB0`) and, on elements $v \in V$, satisfies $\ell_B\bigl(v(\,\cdot\,n(x))\bigr) = \ell_B(v)$ for all $x \in K_p$ (`hℓBN`), $\ell_B\bigl(v(\,\cdot\,\mathrm{diag}(a,1))\bigr) = \chi_1(a)\,\ell_B(v)$ (`hℓBD`) and $\ell_B\bigl(v(\,\cdot\,a\cdot 1_2)\bigr) = \omega_1(a)\,\ell_B(v)$ (`hℓBZ`) for all units $a$; that is, $V$ carries a Borel eigenfunctional.
--
--   Write $c = \theta_0(\varpi)\,\mu_0(\varpi)\,\mu_1(\varpi)$, where $\varpi$ is taken as the unit `Units.mk0` of its non-zero image in $K_p$. The conclusion asserts: for every Haar measure $\mu_2$ on $GL_2(K_p)$ and every Haar measure $\mu_{N_2}$ on the range of `unipotentGL2Hom`, for every $w_2 \in V$, all polynomials $P_1, P_2 \in \mathbb{C}[X]$, integers $m_1, m_2$ and reals $\sigma_4, \sigma_5$, the following implication holds. Suppose first that for all $s$ with $\operatorname{Re} s > \sigma_4$,
--   $$\mathrm{rsLocalIntegral}\bigl(\mu_2, N, \mu_{N_2}, g\mapsto|\det g|, s+\tfrac12, W_\varphi, F\bigr)\cdot\bigl(1 - c\,q^{-2s}\bigr) = q^{m_1 s}P_1(q^{-s}),$$
--   where the spectral integral is $\int (W_\varphi(g)F(g))\,|\det g|^{(s+1/2)-1/2}$ against $\mu_2$ given the density [`HaarQuotient.density`](def/HaarQuotient.html#L25) relative to the unipotent subgroup with its Haar measure, with $W_\varphi(g) = \int_{K_p}\psi_p(x)\,\varphi\bigl(\mathrm{antidiag}\cdot n(x)\cdot g\bigr)\,dx$ the Jacquet integral of $\varphi$ and $F(g) = w_2(g)\,\Phi_2(g_{10},g_{11})$. Suppose second that for all $s$ with $\operatorname{Re} s > \sigma_5$ the corresponding dual integral satisfies
--   $$\mathrm{rsLocalIntegral}\bigl(\mu_2, N, \mu_{N_2}, g\mapsto|\det g|, s+\tfrac12, W_\varphi^{d}, F^{d}\bigr)\cdot\bigl(1 - c^{-1}q^{-2}q^{-2s}\bigr) = q^{m_2 s}P_2(q^{-s}),$$
--   where $W_\varphi^{d}(g) = \int_{K_p}\psi_p(x)\,\varphi\bigl(\mathrm{antidiag}\cdot n(x)\cdot (w_{0,p}\,{}^{t}g^{-1})\bigr)\,dx$ and
--   $$F^{d}(g) = |\det g|\;w_2\bigl(w_{0,p}\,{}^{t}g^{-1}\bigr)\int_{K_p\times K_p}\Phi_2(u)\,\psi_p\bigl(u_1 g_{10} + u_2 g_{11}\bigr)\,du,$$
--   the inner integral taken against the product of two copies of the self-dual measure. Then for every $s \in \mathbb{C}$,
--   $$q^{m_2 s}P_2(q^{-s})\bigl(1 - c\,q^{2s}\bigr) = \Bigl(\mu_0(-1)\mu_1(-1)\,E_0E_1\,q^{-(e_0+e_1)s}\Bigr)\cdot\Bigl(q^{m_1(-s)}P_1(q^{s})\Bigr)\cdot\bigl(1 - c^{-1}q^{-2}q^{-2s}\bigr).$$
--   Thus the assertion is an identity between the Laurent numerators of the two centre-cleared local Rankin–Selberg integrals, with the Euler-type clearing factors transformed as displayed; it does not assert the existence of such Laurent forms, which is hypothesised.
--
--   This is the local $GL_2 \times GL_2$ functional equation at a finite place, in centre-cleared form: the Rankin–Selberg integral of a principal-series Jacquet–Godement section against a Whittaker vector for a representation admitting a Borel eigenfunctional, with its dual integral, satisfy a functional equation of monomial type whose constant is built from $\mu_0(-1)\mu_1(-1)$ and the torus gamma factors $E_0, E_1$, $e_0, e_1$. It is the principal-series branch of the local core step, invoked by [`LanglandsTunnell.RankinSelberg.forall_rsLocalIntegral22_schwartz_centralCleared_laurentFE_of_principalSeries2_of_forall_torusZeta_fe`](thm.html#LanglandsTunnell.RankinSelberg.forall_rsLocalIntegral22_schwartz_centralCleared_laurentFE_of_principalSeries2_of_forall_torusZeta_fe), which combines it with the cuspidal branch; the resulting local functional equations feed the converse-theorem input of the Langlands–Tunnell step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral22_schwartz_centralCleared_laurentFE_of_principalSeries2_of_forall_torusZeta_fe_of_borelEigenfunctional.lean

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

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open LanglandsTunnell.RankinSelberg

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

theorem LanglandsTunnell.RankinSelberg.forall_rsLocalIntegral22_schwartz_centralCleared_laurentFE_of_principalSeries2_of_forall_torusZeta_fe_of_borelEigenfunctional
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
    (χ₁ ω₁ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (ℓB : (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) →ₗ[ℂ] ℂ)
    (hℓB0 : ∃ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ℓB v ≠ 0)
    (hℓBN : ∀ (x : (p.adicCompletion ℚ)), ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ℓB (fun g : GL (Fin 2) (p.adicCompletion ℚ) => v (g * unipotent x)) = ℓB v)
    (hℓBD : ∀ (a : (p.adicCompletion ℚ)ˣ), ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ℓB (fun g : GL (Fin 2) (p.adicCompletion ℚ) => v (g * diagOne a)) = ((χ₁ a : ℂˣ) : ℂ) * ℓB v)
    (hℓBZ : ∀ (a : (p.adicCompletion ℚ)ˣ), ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ℓB (fun g : GL (Fin 2) (p.adicCompletion ℚ) => v (g * Matrix.GeneralLinearGroup.scalar (Fin 2) a)) = ((ω₁ a : ℂˣ) : ℂ) * ℓB v)
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
