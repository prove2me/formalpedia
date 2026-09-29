-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral22_schwartz_clearedFE_of_principalSeries2_of_forall_torusZeta_fe_ed2
-- name    : LanglandsTunnell.RankinSelberg.forall_rsLocalIntegral22_schwartz_clearedFE_of_principalSeries2_of_forall_torusZeta_fe_ed2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/cfe8f0a6-dfed-57b0-a94b-ed4ad8feb549
-- title:
--   Cleared GL₂× GL₂ local functional equation: principal series case
-- statement:
--   Throughout, $p$ is a height-one prime of $\mathcal O_{\mathbb Q}$, $F = \mathbb Q_p$ denotes the completion `p.adicCompletion ℚ`, $N_p =$ `Ideal.absNorm p.asIdeal` is the residue cardinality, $\psi =$ [`NumberField.StandardAddChar.psiLocal ℚ p`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65) is the standard local additive character, $dx =$ `selfDualHaarAt ℚ p` is the additive Haar measure on $F$ normalised by the level of $\psi$, $|\cdot| =$ `modulus` is the module of $F$, and the measure on $F^\times$ is the pullback along `Units.val` of `mulMeasure (selfDualHaarAt ℚ p)`, i.e. of $dx$ restricted to $F\setminus\{0\}$ with density $|x|^{-1}$. For $y \in F^\times$, `diagOne y` is the matrix $\mathrm{diag}(y,1)$ in $GL_2(F)$; `unipotent x` and `upperUnipotent2 p x` are $\begin{pmatrix}1&x\\0&1\end{pmatrix}$, `antidiagonal2 p` is $\begin{pmatrix}0&1\\1&0\end{pmatrix}$, `transposeInvN (Fin 2) g` is ${}^{t}g^{-1}$, and the range of `unipotentGL2Hom` is the group of upper unipotent matrices.
--
--   The inducing data consist of two multiplicative characters $\mu_0,\mu_1 : F^\times \to \mathbb C^\times$ (`μ`), assumed locally constant (`hμ`), together with real exponents $\sigma_0,\sigma_1$ (`σ`) such that $\|\mu_i(a)\| = \|a\|^{\sigma_i}$ for all $a$ (`hσ`) and $\sigma_1 < \sigma_0$ (`h01`), and a function $\varphi$ on $GL_2(F)$ lying in `principalSeries2 p μ` (`hφ`), that is: $\varphi$ is locally constant, left invariant under the upper unipotent matrices, and satisfies $\varphi(\mathrm{diag}(a_0,a_1) g) = \mu_0(a_0)\mu_1(a_1)\,(\|a_0\|/\|a_1\|)^{1/2}\,\varphi(g)$ for all $a \in (F^\times)^2$ and $g$. Further, $\Phi_2 : F \times F \to \mathbb C$ is locally constant with compact support (`hΦ₂`).
--
--   The second factor is given by a function $w_2^{\mathrm{base}}$ on $GL_2(F)$ subject to: the Whittaker transformation law $w_2^{\mathrm{base}}\big(\begin{pmatrix}1&x\\0&1\end{pmatrix}g\big) = \psi(x)\,w_2^{\mathrm{base}}(g)$ (`hw₂law`); right invariance under [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N`](def/AdelicDock_LocalEmbedding.html#L178), the preimage under the local embedding $GL_2(F) \to GL_2(\mathbb A_{\mathbb Q}^{\mathrm{fin}})$ of the finite level-one subgroup of level $N$, for a nonzero ideal $N$ of $\mathcal O_{\mathbb Q}$ (`hN`, `hw₂K`); non-vanishing $w_2^{\mathrm{base}} \neq 0$ (`hw₂ne`); an irreducibility condition (`hw₂irr`): every nonzero element $w$ of the span $V$ of the right translates $g \mapsto w_2^{\mathrm{base}}(gh)$ has $w_2^{\mathrm{base}}$ in the span of its own right translates; an admissibility condition (`hw₂adm`): for every open subgroup $U \le GL_2(F)$ there is a finite set $B$ of functions whose span contains all right $U$-invariant elements of $V$; and a central character condition $w_2^{\mathrm{base}}(z\cdot 1_2 \, g) = \theta_0(z)\,w_2^{\mathrm{base}}(g)$ for a character $\theta_0$ of $F^\times$ (`hcentral`). Two Weyl elements are fixed: $w_{0,p}$ with matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ (`hw₀p`) and $w_J$ with matrix $\begin{pmatrix}0&1\\-1&0\end{pmatrix}$ (`hwJ`).
--
--   The constants $E : \mathrm{Fin}\,2 \to \mathbb C$ and $e : \mathrm{Fin}\,2 \to \mathbb Z$ enter through the two $GL_2 \times GL_1$ functional-equation hypotheses `hfe0` and `hfe1`, which are the same statement for $i = 0$ and $i = 1$ respectively: for every $w \in V$ there exist polynomials $P, P^\vee \in \mathbb C[T]$, integers $m, m^\vee$ and reals $\sigma_0', \sigma_1'$ such that for $\operatorname{Re} s > \sigma_0'$ the function $y \mapsto w(\mathrm{diag}(y,1))\,\mu_i(y)\,|y|^{s-1/2}$ is integrable on $F^\times$ with integral $N_p^{ms}P(N_p^{-s})$; for $\operatorname{Re} s < \sigma_1'$ the function $y \mapsto w(\mathrm{diag}(y,1)w_J)\,\mu_i(y)^{-1}\theta_0(y)^{-1}|y|^{1/2-s}$ is integrable on $F^\times$ with integral $N_p^{m^\vee s}P^\vee(N_p^{-s})$; and for all $s \in \mathbb C$ the identity $N_p^{m^\vee s}P^\vee(N_p^{-s}) = E_i\,N_p^{e_i s}\cdot N_p^{m s}P(N_p^{-s})$ holds.
--
--   Under these hypotheses the conclusion is the following, with $GL_2(F)$ and $F$ carrying their Borel structures. Let $\mu_2$ be any Haar measure on $GL_2(F)$ and $\mu_{N_2}$ any Haar measure on the upper unipotent subgroup; the pair is used only through the measure $\mu_2$ weighted by [`HaarQuotient.density`](def/HaarQuotient.html#L25), the explicit density built from the `weight` function, which plays the role of the quotient measure on $N_2 \backslash GL_2(F)$. Let $w_2 \in V$, let $P, P^\vee, Q, Q^\vee \in \mathbb C[T]$ with $Q \neq 0$ and $Q^\vee \neq 0$, let $m, m^\vee \in \mathbb Z$ and $\sigma_2, \sigma_3 \in \mathbb R$. Write
--   $$W'(g) = \int_F \psi(x)\,\varphi\Big(\begin{pmatrix}0&1\\1&0\end{pmatrix}\begin{pmatrix}1&x\\0&1\end{pmatrix} g\Big)\,dx,\qquad F_1(g) = w_2(g)\,\Phi_2(g_{10}, g_{11}),$$
--   $$W'^{\vee}(g) = \int_F \psi(x)\,\varphi\Big(\begin{pmatrix}0&1\\1&0\end{pmatrix}\begin{pmatrix}1&x\\0&1\end{pmatrix}\,w_{0,p}\,{}^{t}g^{-1}\Big)\,dx,$$
--   $$F_1^{\vee}(g) = |\det g|\;w_2\big(w_{0,p}\,{}^{t}g^{-1}\big)\int_{F^2}\Phi_2(u)\,\psi\big(u_1 g_{10} + u_2 g_{11}\big)\,du .$$
--   Assume four hypotheses: for $\operatorname{Re} s > \sigma_2$ the function $g \mapsto W'(g)F_1(g)\,|\det g|^{s + 1/2 - 1/2}$ is integrable for the weighted measure; for $\operatorname{Re} s > \sigma_3$ the function $g \mapsto W'^{\vee}(g)F_1^{\vee}(g)\,|\det g|^{s+1/2-1/2}$ is integrable for the weighted measure; for $\operatorname{Re} s > \sigma_2$,
--   $$\mathrm{rsLocalIntegral}\big(\mu_2, N_2, \mu_{N_2}, |\det \cdot|, s + \tfrac12, W', F_1\big)\cdot Q(N_p^{-s}) = N_p^{ms}\,P(N_p^{-s});$$
--   and for $\operatorname{Re} s > \sigma_3$,
--   $$\mathrm{rsLocalIntegral}\big(\mu_2, N_2, \mu_{N_2}, |\det \cdot|, s + \tfrac12, W'^{\vee}, F_1^{\vee}\big)\cdot Q^\vee(N_p^{-s}) = N_p^{m^\vee s}\,P^\vee(N_p^{-s}),$$
--   where [`RSCarrier.rsLocalIntegral`](def/LanglandsTunnell_RSCarrier.html#L16) of data $(\mu_2, H, \mu_H, \delta, s, W, F)$ denotes $\int (W g)(F g)\,\delta(g)^{s - 1/2}$ against $\mu_2$ weighted by [`HaarQuotient.density H μ_H`](def/HaarQuotient.html#L25).
--
--   Then for every $s \in \mathbb C$,
--   $$1\cdot\Big(N_p^{m^\vee s}\,P^\vee(N_p^{-s})\Big)\cdot Q(N_p^{s}) \;=\; \Big(\mu_0(-1)\mu_1(-1)\,E_0E_1\cdot N_p^{-(e_0+e_1)s}\Big)\cdot\Big(N_p^{m(-s)}\,P(N_p^{s})\Big)\cdot Q^\vee(N_p^{-s}),$$
--   the leading factor $1$ being the constant polynomial $1$ evaluated at $N_p^{s}$ and the constant $\mu_0(-1)\mu_1(-1)E_0E_1$ appearing as `Polynomial.C` of that value evaluated at $N_p^{s}$. Equivalently, after clearing the denominators $Q, Q^\vee$, the dual integral at $s$ equals $\mu_0(-1)\mu_1(-1)E_0E_1\,N_p^{-(e_0+e_1)s}$ times the first integral at $-s$, the two integrals being given by the rational functions of $N_p^{\pm s}$ exhibited in the hypotheses. Note that the identity is asserted for all $s \in \mathbb C$, with no convergence restriction, and for arbitrary presentations $(P,Q,m)$ and $(P^\vee,Q^\vee,m^\vee)$ satisfying those hypotheses.
--
--   This is the local functional equation for the $GL_2 \times GL_2$ Rankin–Selberg integral with a Schwartz–Bruhat function, in the case where one factor is a principal series $I(\mu_0,\mu_1)$ and the other is given by the right translates of a Whittaker function; the monomial factor $\mu_0(-1)\mu_1(-1)E_0E_1N_p^{-(e_0+e_1)s}$ expresses multiplicativity of the $\gamma$-factor in the principal-series variable, in a form with denominators cleared so that the identity holds for all $s$. It feeds the corresponding $GL_3 \times GL_2$ statement [`LanglandsTunnell.RankinSelberg.forall_rsLocalIntegral_clearedFE_prod_of_jacquetWhittaker3_of_forall_torusZeta_fe_core_of_chamber`](thm.html#LanglandsTunnell.RankinSelberg.forall_rsLocalIntegral_clearedFE_prod_of_jacquetWhittaker3_of_forall_torusZeta_fe_core_of_chamber).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral22_schwartz_clearedFE_of_principalSeries2_of_forall_torusZeta_fe_ed2.lean

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

theorem LanglandsTunnell.RankinSelberg.forall_rsLocalIntegral22_schwartz_clearedFE_of_principalSeries2_of_forall_torusZeta_fe_ed2
    (p : HeightOneSpectrum (𝓞 ℚ))

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
          ∀ (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ), Q ≠ 0 → Qd ≠ 0 →

            (∀ s : ℂ, σ₂ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                ((fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                    φ (antidiagonal2 p * upperUnipotent2 p x * g) ∂(selfDualHaarAt ℚ p)) g * (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  w₂ g * Φ₂ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) →
            (∀ s : ℂ, σ₃ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                ((fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                    φ (antidiagonal2 p * upperUnipotent2 p x * (w₀p * transposeInvN (Fin 2) g)) ∂(selfDualHaarAt ℚ p)) g * (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g) *
                    (∫ u : p.adicCompletion ℚ × p.adicCompletion ℚ, Φ₂ u *
                      NumberField.StandardAddChar.psiLocal ℚ p
                        (u.1 * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 + u.2 * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)
                    ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)))) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) →

            (∀ s : ℂ, σ₂ < s.re →
              RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                (s + 1 / 2)
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                    φ (antidiagonal2 p * upperUnipotent2 p x * g) ∂(selfDualHaarAt ℚ p))
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  w₂ g * Φ₂ ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)) * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) →
            (∀ s : ℂ, σ₃ < s.re →
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
                    ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)))) * Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) →

            (∀ s : ℂ,
              ((1 : Polynomial ℂ)).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) *
                  ((Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) *
                  Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) =
                ((Polynomial.C ((((μ 0 (-1) : ℂˣ) : ℂ) * ((μ 1 (-1) : ℂˣ) : ℂ)) * (E 0 * E 1))).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) * (Ideal.absNorm p.asIdeal : ℂ) ^ (((-(e 0 + e 1) : ℤ) : ℂ) * s)) *
                  ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s)) *
                  Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) := by sorry
