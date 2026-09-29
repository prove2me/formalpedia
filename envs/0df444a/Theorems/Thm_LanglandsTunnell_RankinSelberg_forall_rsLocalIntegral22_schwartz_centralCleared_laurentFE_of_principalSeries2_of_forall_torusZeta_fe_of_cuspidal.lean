-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral22_schwartz_centralCleared_laurentFE_of_principalSeries2_of_forall_torusZeta_fe_of_cuspidal
-- name    : LanglandsTunnell.RankinSelberg.forall_rsLocalIntegral22_schwartz_centralCleared_laurentFE_of_principalSeries2_of_forall_torusZeta_fe_of_cuspidal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/e25e47e3-2a05-57c0-a26c-09643a6cf9ee
-- title:
--   Centre-cleared local functional equation for GL₂× GL₂: cuspidal branch
-- statement:
--   Throughout, $p$ is a point of the height-one spectrum of the ring of integers of $\mathbb{Q}$, $K_p$ denotes `p.adicCompletion ℚ` with ring of integers `p.adicCompletionIntegers ℚ`, and $q$ denotes the absolute norm `Ideal.absNorm p.asIdeal`. The additive character $\psi_p$ is [`NumberField.StandardAddChar.psiLocal ℚ p`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65), the restriction to $K_p$ of the standard adelic character of $\mathbb{Q}$, and the additive measure on $K_p$ is `selfDualHaarAt ℚ p`, the additive Haar measure of the ring of integers rescaled by $q^{-\mathrm{level}(\psi_p)/2}$. Integrals over $K_p^\times$ are taken against `Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))`, the pull-back to the units of the measure $dx$ weighted by $\mathrm{modulus}(x)^{-1}$ off $0$; here $\mathrm{modulus}$ is the module of a scalar, i.e. the distributive Haar character of $x$ for $x\neq 0$ and $0$ at $0$. Measurable structures are the Borel ones: `localBorel ℚ p` on $K_p$ and `localGLBorel ℚ p` on $GL_2(K_p)$.
--
--   The data are as follows. A uniformiser: an element $\varpi$ of the ring of integers whose image $\varpi\in K_p$ is nonzero (`hπ`) and has valuation $\exp(-1)$ (`hϖ`). Chamber principal-series data: a pair $\mu=(\mu_0,\mu_1)$ of homomorphisms $K_p^\times\to\mathbb{C}^\times$, each locally constant (`hμ`), exponents $\sigma_0,\sigma_1\in\mathbb{R}$ with $\|\mu_i(a)\|=\|a\|^{\sigma_i}$ for all units $a$ (`hσ`) and $\sigma_1<\sigma_0$ (`h01`), and a function $\varphi:GL_2(K_p)\to\mathbb{C}$ lying in `principalSeries2 p μ`, that is: $\varphi$ is locally constant, invariant under left translation by the upper unipotents `upperUnipotent2 p x` $=\begin{pmatrix}1&x\\0&1\end{pmatrix}$, and satisfies $\varphi(\mathrm{diag}(a)g)=\mathrm{torusChar2}(\mu)(a)\,\mathrm{halfModulus2}(a)\,\varphi(g)$ for diagonal $a$. A Schwartz–Bruhat function on the plane: $\Phi_2:K_p\times K_p\to\mathbb{C}$ locally constant with compact support (`hΦ₂`).
--
--   Whittaker-vector data: a homomorphism $\theta_0:K_p^\times\to\mathbb{C}^\times$, a nonzero ideal $N$ of the ring of integers of $\mathbb{Q}$ (`hN`), and a function $w_2^{\mathrm{base}}:GL_2(K_p)\to\mathbb{C}$ subject to six hypotheses: `hw₂law`, the Whittaker law $w_2^{\mathrm{base}}(u(x)g)=\psi_p(x)\,w_2^{\mathrm{base}}(g)$ for the unipotent $u(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$; `hw₂K`, right invariance under the subgroup [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N`](def/AdelicDock_LocalEmbedding.html#L178), the pull-back along the local embedding at $p$ of the finite-adelic level-one subgroup of $N$; `hw₂ne`, $w_2^{\mathrm{base}}\neq 0$; `hw₂irr`, irreducibility in the form that every nonzero element $w$ of the $\mathbb{C}$-span $V$ of the right translates $g\mapsto w_2^{\mathrm{base}}(gh)$ has $w_2^{\mathrm{base}}$ in the span of the right translates of $w$; `hw₂adm`, admissibility in the form that for every open subgroup $U$ of $GL_2(K_p)$ there is a finite set $B$ of functions such that every $U$-right-invariant member of $V$ lies in the span of $B$; and `hcentral`, the central character law $w_2^{\mathrm{base}}(zI\cdot g)=\theta_0(z)\,w_2^{\mathrm{base}}(g)$. Two Weyl elements are fixed: $w_{0p}$ with matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ (`hw₀p`) and $w_J$ with matrix $\begin{pmatrix}0&1\\-1&0\end{pmatrix}$ (`hwJ`).
--
--   Torus-zeta functional equations: constants $E:\mathrm{Fin}\,2\to\mathbb{C}$ and $e:\mathrm{Fin}\,2\to\mathbb{Z}$, together with two hypotheses `hfe0` and `hfe1`, of identical shape for $i=0$ and $i=1$ respectively: for every $w\in V$ there exist $P,P^{\vee}\in\mathbb{C}[X]$, $m,m^{\vee}\in\mathbb{Z}$ and $\sigma_0',\sigma_1'\in\mathbb{R}$ such that (a) for $\mathrm{Re}\,s>\sigma_0'$ the function $y\mapsto w(\mathrm{diag}(y,1))\,\mu_i(y)\,|y|^{\,s-1/2}$ is integrable on $K_p^\times$ and its integral equals $q^{ms}P(q^{-s})$; (b) for $\mathrm{Re}\,s<\sigma_1'$ the function $y\mapsto w(\mathrm{diag}(y,1)\,w_J)\,\mu_i(y)^{-1}\theta_0(y)^{-1}|y|^{\,1/2-s}$ is integrable and its integral equals $q^{m^{\vee}s}P^{\vee}(q^{-s})$; and (c) for all $s\in\mathbb{C}$, $q^{m^{\vee}s}P^{\vee}(q^{-s})=E_i\,q^{(e_i)s}\cdot q^{ms}P(q^{-s})$. Here $\mathrm{diag}(y,1)$ is `diagOne y`. Finally, the cuspidality hypothesis `hcusp`: for every $v\in V$ there is $N_0\in\mathbb{Z}$ with $v(\mathrm{diag}(y,1))=0$ whenever $\mathrm{v}(y)\le\exp(N_0)$, i.e. the associated Kirillov function vanishes in a neighbourhood of $0$.
--
--   The conclusion is a statement about all Haar measures $\mu_2$ on $GL_2(K_p)$ and $\mu_{N_2}$ on the range of `unipotentGL2Hom` (the upper unipotent subgroup $\{u(x)\}$), all $w_2\in V$, all $P_1,P_2\in\mathbb{C}[X]$, all $m_1,m_2\in\mathbb{Z}$ and all $\sigma_4,\sigma_5\in\mathbb{R}$. Write $c=\theta_0(\varpi)\mu_0(\varpi)\mu_1(\varpi)$, where $\varpi$ is viewed as the unit `Units.mk0` provided by `hπ`, and write $\mathrm{RS}(s;W,F)$ for [`RSCarrier.rsLocalIntegral μ₂`](def/LanglandsTunnell_RSCarrier.html#L16) applied to the unipotent subgroup with $\mu_{N_2}$, to the modulus character $\delta(g)=\mathrm{modulus}(\det g)$, at the point $s+1/2$, with data $W,F$; by definition this is $\int (W(g)F(g))\,\delta(g)^{\,s}$ against $\mu_2$ weighted by the quotient density [`HaarQuotient.density`](def/HaarQuotient.html#L25) of the unipotent subgroup.
--
--   Two hypotheses are assumed on this data. First, for all $s$ with $\mathrm{Re}\,s>\sigma_4$,
--   $$\mathrm{RS}\bigl(s;\,g\mapsto\textstyle\int_{K_p}\psi_p(x)\,\varphi(a_2\,u^+(x)\,g)\,dx,\ g\mapsto w_2(g)\,\Phi_2(g_{10},g_{11})\bigr)\cdot\bigl(1-c\,q^{-2s}\bigr)=q^{m_1 s}P_1(q^{-s}),$$
--   where $a_2=$ `antidiagonal2 p` $=\begin{pmatrix}0&1\\1&0\end{pmatrix}$, $u^+(x)=$ `upperUnipotent2 p x`, and $g_{10},g_{11}$ are the entries of the bottom row of $g$. Second, for all $s$ with $\mathrm{Re}\,s<\sigma_5$,
--   $$\mathrm{RS}\bigl(s;\,W^{\vee},F^{\vee}\bigr)\cdot\bigl(1-c^{-1}q^{-2}q^{-2s}\bigr)=q^{m_2 s}P_2(q^{-s}),$$
--   with $W^{\vee}(g)=\int_{K_p}\psi_p(x)\,\varphi\bigl(a_2\,u^+(x)\,(w_{0p}\cdot{}^{t}g^{-1})\bigr)\,dx$ and $F^{\vee}(g)=\mathrm{modulus}(\det g)\cdot w_2(w_{0p}\cdot{}^{t}g^{-1})\cdot\int_{K_p\times K_p}\Phi_2(u)\,\psi_p(u_1g_{10}+u_2g_{11})\,du$, the last integral taken against the product of two copies of `selfDualHaarAt ℚ p`; here ${}^{t}g^{-1}$ is `transposeInvN (Fin 2) g`, the transpose of the inverse of $g$.
--
--   Under these two hypotheses the assertion is that for every $s\in\mathbb{C}$,
--   $$q^{m_2 s}P_2(q^{-s})\cdot\bigl(1-c\,q^{2s}\bigr)=\Bigl(\mu_0(-1)\mu_1(-1)\,E_0E_1\,q^{-(e_0+e_1)s}\Bigr)\cdot\Bigl(q^{-m_1 s}P_1(q^{s})\Bigr)\cdot\bigl(1-c^{-1}q^{-2}q^{-2s}\bigr),$$
--   an identity of functions of $s$ on all of $\mathbb{C}$, with no convergence restriction.
--
--   This is the local functional equation at a finite place for the $GL_2\times GL_2$ Rankin–Selberg integral of a chamber principal series against a Whittaker vector, in the centre-cleared normalisation in which both sides carry the Euler-type factor attached to $\theta_0\mu_0\mu_1(\varpi)$; it is the branch of the Kirillov dichotomy in which the Whittaker functions vanish near $0$ on the torus. It feeds the version [`LanglandsTunnell.RankinSelberg.forall_rsLocalIntegral22_schwartz_centralCleared_laurentFE_of_principalSeries2_of_forall_torusZeta_fe`](thm.html#LanglandsTunnell.RankinSelberg.forall_rsLocalIntegral22_schwartz_centralCleared_laurentFE_of_principalSeries2_of_forall_torusZeta_fe), where the cuspidality hypothesis is discharged, and serves as local input to the converse-theorem step of the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral22_schwartz_centralCleared_laurentFE_of_principalSeries2_of_forall_torusZeta_fe_of_cuspidal.lean

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

theorem LanglandsTunnell.RankinSelberg.forall_rsLocalIntegral22_schwartz_centralCleared_laurentFE_of_principalSeries2_of_forall_torusZeta_fe_of_cuspidal
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
    (hcusp : ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ N₀ : ℤ, ∀ y : (p.adicCompletion ℚ)ˣ, Valued.v (y : (p.adicCompletion ℚ)) ≤ WithZero.exp N₀ → v (diagOne y) = 0)
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
