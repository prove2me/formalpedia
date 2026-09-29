-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral_clearedFE_prod_of_jacquetWhittaker3_of_forall_torusZeta_fe_core_of_chamber
-- name    : LanglandsTunnell.RankinSelberg.forall_rsLocalIntegral_clearedFE_prod_of_jacquetWhittaker3_of_forall_torusZeta_fe_core_of_chamber
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/a8e442ee-067d-5e1b-9367-39a71f31139a
-- title:
--   Cleared GL₃× GL₂ functional equation in the positive chamber
-- statement:
--   Throughout, $p$ is a point of the height-one spectrum of $\mathcal O_{\mathbb Q}$, so that $\mathbb Q_p :=$ `p.adicCompletion ℚ` is the associated completion, and $N_p :=$ `Ideal.absNorm p.asIdeal` denotes the absolute norm of the corresponding prime ideal. For $a \in \mathbb Q_p$, `modulus a` is the module of $a$ (the value of the distributive Haar character at $a$ when $a \neq 0$, and $0$ otherwise), `selfDualHaarAt ℚ p` is the additive Haar measure on $\mathbb Q_p$ normalised by the level of the local standard additive character `psiLocal ℚ p`, and `mulMeasure` turns it into the multiplicative measure $|x|^{-1}\,dx$ on $\mathbb Q_p \setminus \{0\}$; the measure used on $\mathbb Q_p^{\times}$ is its pull-back along the inclusion `Units.val`.
--
--   **Inducing data on $GL_3$.** Given a triple $\lambda = (\lambda_0,\lambda_1,\lambda_2)$ of homomorphisms $\mathbb Q_p^{\times} \to \mathbb C^{\times}$, each locally constant (`hlam`), a triple of real exponents $\sigma$ with $\|\lambda_i(a)\| = \|a\|^{\sigma_i}$ for all $i$ and all $a \in \mathbb Q_p^{\times}$ (`hσ`), subject to the chamber conditions $\sigma_1 < \sigma_0$ (`h01`) and $\sigma_2 < \sigma_1$ (`h12`), a function $\Phi$ on $\mathbb Q_p^3$ that is locally constant and compactly supported (`hΦ`), and elements $x,y,z \in \mathbb Q_p$, the function $W_3$ on $GL_3(\mathbb Q_p)$ is required by `hW₃` to be
--   $$W_3(h) \;=\; \mathrm{jacquetWhittaker3}_p(\lambda,\Phi)\bigl(\mathrm{diag}(1,-1,1)\, h \, n(x,y,z)\, w\bigr),$$
--   where $n(x,y,z) =$ `upperUnipotent3 x y z` is the upper triangular unipotent matrix with entries $x$ (position $(0,1)$), $y$ (position $(1,2)$), $z$ (position $(0,2)$), $w =$ `antidiagonal3 p` is the antidiagonal permutation matrix, and `jacquetWhittaker3 p lam Φ g` is `jacquetValue p` applied to the right translate by $g$ (via `gl3AmbientRightTranslate`) of the big-cell section `cellSectionOf p lam Φ`, itself the indicator of `bigCell3 p` times $g \mapsto$ `cellValue p lam g * Φ (cellRatio p g)`; here `jacquetValue p u = jacquetTruncated3 p (jacquetLevel p u) u` is the truncated unipotent integral at the level determined by $u$.
--
--   **Data on $GL_2$.** Further given are a homomorphism $\theta_0 : \mathbb Q_p^{\times} \to \mathbb C^{\times}$, a nonzero ideal $N$ of $\mathcal O_{\mathbb Q}$ (`hN`), and a function $w_{2,\mathrm{base}} : GL_2(\mathbb Q_p) \to \mathbb C$ subject to the following hypotheses: the Whittaker transformation law `hw₂law`, $w_{2,\mathrm{base}}(n(x)g) = \psi_p(x)\, w_{2,\mathrm{base}}(g)$ for the unipotent $n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$ and $\psi_p =$ `psiLocal ℚ p`; right invariance `hw₂K` under [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N`](def/AdelicDock_LocalEmbedding.html#L178), the pull-back along the local embedding `localEmbed` of the level-one subgroup `finiteLevelOne` of $GL_2$ of the finite adeles attached to $N$; non-vanishing `hw₂ne`, $w_{2,\mathrm{base}} \neq 0$; an irreducibility condition `hw₂irr`, that every nonzero element $w$ of the span $V$ over $\mathbb C$ of the right translates $g \mapsto w_{2,\mathrm{base}}(gh)$, $h \in GL_2(\mathbb Q_p)$, has $w_{2,\mathrm{base}}$ in the span of the right translates of $w$; an admissibility condition `hw₂adm`, that for every open subgroup $U$ of $GL_2(\mathbb Q_p)$ there is a finite set $B$ of functions such that every $w \in V$ which is right $U$-invariant lies in the span of $B$; and the central character condition `hcentral`, $w_{2,\mathrm{base}}(z\cdot g) = \theta_0(z)\, w_{2,\mathrm{base}}(g)$ for scalar matrices $z \in \mathbb Q_p^{\times}$. Two Weyl elements are fixed: $w_{0,p}$ with matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ (`hw₀p`) and $w_J$ with matrix $\begin{pmatrix}0&1\\-1&0\end{pmatrix}$ (`hwJ`).
--
--   **The three $GL_2 \times GL_1$ functional equations.** Constants $E : \mathrm{Fin}\,3 \to \mathbb C$ and exponents $e : \mathrm{Fin}\,3 \to \mathbb Z$ are given, and for each $i \in \{0,1,2\}$ the hypothesis `hfe`$i$ asserts: for every $w \in V$ there exist polynomials $P, P^{\vee} \in \mathbb C[T]$, integers $m, m^{\vee}$ and reals $\sigma_0', \sigma_1'$ such that (a) for $\operatorname{Re} s > \sigma_0'$ the function $y \mapsto w(\mathrm{diag}(y,1))\,\lambda_i(y)\,|y|^{s-1/2}$ is integrable on $\mathbb Q_p^{\times}$ for the above measure, and (b) its integral equals $N_p^{m s}\,P(N_p^{-s})$; (c) for $\operatorname{Re} s < \sigma_1'$ the function $y \mapsto w(\mathrm{diag}(y,1)\,w_J)\,\lambda_i(y)^{-1}\theta_0(y)^{-1}|y|^{1/2-s}$ is integrable, and (d) its integral equals $N_p^{m^{\vee} s}\,P^{\vee}(N_p^{-s})$; and (e) for all $s \in \mathbb C$,
--   $$N_p^{m^{\vee}s}\,P^{\vee}(N_p^{-s}) \;=\; \bigl(E_i\,N_p^{e_i s}\bigr)\cdot N_p^{m s}\,P(N_p^{-s}).$$
--   Here $\mathrm{diag}(y,1) =$ `diagOne y`.
--
--   **Conclusion.** With $GL_2(\mathbb Q_p)$ carrying the Borel $\sigma$-algebra `localGLBorel ℚ p` and the corresponding Borel space instance, the assertion is: for every Haar measure $\mu_2$ on $GL_2(\mathbb Q_p)$, every Haar measure $\mu_{N_2}$ on the range of `unipotentGL2Hom` (the subgroup of upper triangular unipotent matrices $\begin{pmatrix}1&x\\0&1\end{pmatrix}$), every $w_2 \in V$, all polynomials $P, P^{\vee}, Q, Q^{\vee} \in \mathbb C[T]$ with $Q \neq 0$ and $Q^{\vee} \neq 0$, all integers $m, m^{\vee}$ and all reals $\sigma_2', \sigma_3'$, if the following four conditions hold, where $\delta(g) :=$ `modulus (det g)` and all integrals over $GL_2(\mathbb Q_p)$ are taken against $\mu_2$ weighted by the density [`HaarQuotient.density`](def/HaarQuotient.html#L25) of the unipotent subgroup relative to $\mu_{N_2}$:
--
--   1. for $\operatorname{Re} s > \sigma_2'$ the function $g \mapsto W_3(\iota(g))\,w_2(g)\,\delta(g)^{s-1/2}$ is integrable, where $\iota =$ `iotaGL` is the embedding $g \mapsto \mathrm{diag}(g,1)$ of $GL_2$ into $GL_3$;
--
--   2. for $\operatorname{Re} s > \sigma_3'$ the function $g \mapsto W_3^{\vee}(\iota(g))\,\bigl(\delta(g)\,w_2(w_{0,p}\,{}^t g^{-1})\bigr)\,\delta(g)^{s-1/2}$ is integrable, where $W_3^{\vee} =$ `dualWhittakerFn3 W₃`, that is $W_3^{\vee}(g) = W_3(w_{\mathrm{long}}\,{}^t g^{-1})$ with $w_{\mathrm{long}} =$ `longWeyl3` the antidiagonal permutation matrix in $GL_3$, and ${}^t g^{-1} =$ `transposeInvN (Fin 2) g`;
--
--   3. for $\operatorname{Re} s > \sigma_2'$,
--   $$\mathrm{rsLocalIntegral}\bigl(\mu_2, \mathcal N, \mu_{N_2}, \delta, s, W_3 \circ \iota, w_2\bigr)\cdot Q(N_p^{-s}) \;=\; N_p^{m s}\,P(N_p^{-s}),$$
--   where $\mathcal N$ is the unipotent subgroup above and [`RSCarrier.rsLocalIntegral`](def/LanglandsTunnell_RSCarrier.html#L16) is by definition $\int (W(g)F(g))\,\delta(g)^{s-1/2}$ against the weighted measure;
--
--   4. for $\operatorname{Re} s > \sigma_3'$,
--   $$\mathrm{rsLocalIntegral}\bigl(\mu_2, \mathcal N, \mu_{N_2}, \delta, s, W_3^{\vee} \circ \iota, \;g \mapsto \delta(g)\,w_2(w_{0,p}\,{}^t g^{-1})\bigr)\cdot Q^{\vee}(N_p^{-s}) \;=\; N_p^{m^{\vee} s}\,P^{\vee}(N_p^{-s});$$
--
--   then for every $s \in \mathbb C$ the cleared functional equation
--   $$1 \cdot \bigl(N_p^{m^{\vee}s}\,P^{\vee}(N_p^{-s})\bigr)\, Q(N_p^{s}) \;=\; \Bigl(\theta_0(-1)\,E_0E_1E_2\cdot N_p^{-(e_0+e_1+e_2)s}\Bigr)\cdot\bigl(N_p^{m\cdot(-s)}\,P(N_p^{s})\bigr)\, Q^{\vee}(N_p^{-s})$$
--   holds, the leading factor $1$ being the evaluation of the constant polynomial $1$ at $N_p^{s}$ and the constant $\theta_0(-1)E_0E_1E_2$ appearing as the evaluation of `Polynomial.C` of it at $N_p^{s}$, with $\theta_0(-1)$ the value of $\theta_0$ at the unit $-1$ of $\mathbb Q_p$.
--
--   This is the local Rankin–Selberg functional equation for $GL_3 \times GL_2$ over $\mathbb Q_p$, in cleared (polynomial) form, for a single right-translated Jacquet–Whittaker generator of the principal series attached to $\lambda$, under the restriction that the exponents of $\lambda$ lie in the positive Weyl chamber $\sigma_0 > \sigma_1 > \sigma_2$; it is the multiplicativity of the $\gamma$-factor in the $GL_3$ variable, the $\varepsilon$-constant being the monomial $\theta_0(-1)E_0E_1E_2 N_p^{-(e_0+e_1+e_2)s}$ built from the three twisted $GL_2 \times GL_1$ functional equations. It feeds the chamber-free version [`LanglandsTunnell.RankinSelberg.forall_rsLocalIntegral_clearedFE_prod_of_jacquetWhittaker3_of_forall_torusZeta_fe_core`](thm.html#LanglandsTunnell.RankinSelberg.forall_rsLocalIntegral_clearedFE_prod_of_jacquetWhittaker3_of_forall_torusZeta_fe_core), whence the local data needed in the converse-theorem step of the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral_clearedFE_prod_of_jacquetWhittaker3_of_forall_torusZeta_fe_core_of_chamber.lean

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

theorem LanglandsTunnell.RankinSelberg.forall_rsLocalIntegral_clearedFE_prod_of_jacquetWhittaker3_of_forall_torusZeta_fe_core_of_chamber
    (p : HeightOneSpectrum (𝓞 ℚ))

    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i))

    (σ : Fin 3 → ℝ)
    (hσ : ∀ (i : Fin 3) (a : (p.adicCompletion ℚ)ˣ), ‖((lam i a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (σ i))
    (h01 : σ 1 < σ 0) (h12 : σ 2 < σ 1)
    (Φ : (Fin 3 → p.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (x y z : p.adicCompletion ℚ)
    (W₃ : LocalGL3 p → ℂ)
    (hW₃ : W₃ = fun h => jacquetWhittaker3 p lam Φ
      (diagonal3 p ![1, -1, 1] * h * (upperUnipotent3 x y z * antidiagonal3 p)))

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

    (E : Fin 3 → ℂ) (e : Fin 3 → ℤ)
    (hfe0 : letI := localBorel ℚ p
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₀ σ₁ : ℝ),
        (∀ s : ℂ, σ₀ < s.re →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y) * ((lam 0 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, σ₀ < s.re →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((lam 0 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y * wJ) * (((lam 0 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
              ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y * wJ) * (((lam 0 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
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
            w (diagOne y) * ((lam 1 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, σ₀ < s.re →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((lam 1 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y * wJ) * (((lam 1 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
              ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y * wJ) * (((lam 1 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ,
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            (E 1 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e 1 : ℂ) * s)) *
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))))
    (hfe2 : letI := localBorel ℚ p
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₀ σ₁ : ℝ),
        (∀ s : ℂ, σ₀ < s.re →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y) * ((lam 2 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, σ₀ < s.re →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((lam 2 y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y * wJ) * (((lam 2 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
              ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y * wJ) * (((lam 2 y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ,
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            (E 2 * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e 2 : ℂ) * s)) *
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))))
    :

    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
          (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
        ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          ∀ (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ), Q ≠ 0 → Qd ≠ 0 →

            (∀ s : ℂ, σ₂ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (W₃ (iotaGL g) * w₂ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) →
            (∀ s : ℂ, σ₃ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (dualWhittakerFn3 W₃ (iotaGL g) * (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) →

            (∀ s : ℂ, σ₂ < s.re →
              RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                  (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                  s (fun g => W₃ (iotaGL g)) w₂ * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) →
            (∀ s : ℂ, σ₃ < s.re →
              RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                  (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                  s (fun g => dualWhittakerFn3 W₃ (iotaGL g)) (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) * Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) →

            (∀ s : ℂ,
              ((1 : Polynomial ℂ)).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) *
                  ((Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) *
                  Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) =
                ((Polynomial.C (((θ₀ (-1) : ℂˣ) : ℂ) * (E 0 * E 1 * E 2))).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) * (Ideal.absNorm p.asIdeal : ℂ) ^ (((-(e 0 + e 1 + e 2) : ℤ) : ℂ) * s)) *
                  ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s)) *
                  Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) := by sorry
