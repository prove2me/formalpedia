-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_rsLocalIntegral_jacquetWhittaker3_mul_centralTate_eq_cpow_mul_eval_and_dual_of_chamber
-- name    : LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral_jacquetWhittaker3_mul_centralTate_eq_cpow_mul_eval_and_dual_of_chamber
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/7c621d4c-9c1c-5b00-beea-d335c8886068
-- title:
--   Cleared local GL₃× GL₂ Rankin–Selberg integrals in a chamber
-- statement:
--   Throughout, $p$ is a height-one prime of the ring of integers of $\mathbb{Q}$, $F = \mathbb{Q}_p$ denotes the completion `p.adicCompletion ℚ`, and $q =$ `Ideal.absNorm p.asIdeal` is the residue cardinality. The element $\varpi \in F^{\times}$ is assumed to satisfy `Valued.v ϖ = WithZero.exp (-1)`, i.e. it is a uniformiser.
--
--   *Inducing data.* A triple $\lambda = (\lambda_0,\lambda_1,\lambda_2)$ of monoid homomorphisms $F^{\times} \to \mathbb{C}^{\times}$ is given, each locally constant (`hlam`), together with real exponents $\sigma : \mathrm{Fin}\,3 \to \mathbb{R}$ such that $\|\lambda_i(a)\| = \|a\|^{\sigma_i}$ for all $a$ (`hσ`) and lying in the chamber $\sigma_2 < \sigma_1 < \sigma_0$ (`h12`, `h01`). A function $\Phi$ on $F^3$ is assumed locally constant with compact support (`hΦ`), and $x,y,z \in F$ are arbitrary. The function $W_3 :$ `LocalGL3 p` $\to \mathbb{C}$ is assumed (`hW₃`) to be the right translate
--   $$W_3(h) = \mathtt{jacquetWhittaker3}\ p\ \lambda\ \Phi\bigl(\mathrm{diag}(1,-1,1)\cdot h\cdot (u(x,y,z)\cdot w)\bigr),$$
--   where $u(x,y,z) =$ `upperUnipotent3 x y z` is the upper triangular unipotent matrix with entries $x$, $y$ above the diagonal and $z$ in the corner, $w =$ `antidiagonal3 p` is the matrix $\begin{pmatrix}0&0&1\\0&1&0\\1&0&0\end{pmatrix}$, and `jacquetWhittaker3 p lam Φ` sends $g$ to `jacquetValue` of the right translate by $g$ of the big-cell section `cellSectionOf p lam Φ`, the latter being the indicator of `bigCell3 p` of $h \mapsto$ `cellValue p lam h * Φ (cellRatio p h)`, and `jacquetValue` of $u$ being `jacquetTruncated3 p (jacquetLevel p u) u`.
--
--   *The $GL_2$ vector.* A monoid homomorphism $\theta_0 : F^{\times} \to \mathbb{C}^{\times}$, a nonzero ideal $N$ of $\mathcal{O}_{\mathbb{Q}}$ (`hN`) and a function $w_{2,\mathrm{base}} : GL_2(F) \to \mathbb{C}$ are given, subject to: the Whittaker transformation law $w_{2,\mathrm{base}}\bigl(\begin{pmatrix}1&x\\0&1\end{pmatrix} g\bigr) = \psi_p(x)\, w_{2,\mathrm{base}}(g)$ for the standard local additive character `psiLocal ℚ p` (`hw₂law`); right invariance under the local level-one group [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N`](def/AdelicDock_LocalEmbedding.html#L178), the pullback along `localEmbed` of `AdelicLevel.finiteLevelOne N` (`hw₂K`); non-vanishing $w_{2,\mathrm{base}} \neq 0$ (`hw₂ne`); an irreducibility condition (`hw₂irr`): every nonzero $w$ in the span of the right translates $g \mapsto w_{2,\mathrm{base}}(gh)$ has $w_{2,\mathrm{base}}$ in the span of its own right translates; an admissibility condition (`hw₂adm`): for every open subgroup $U \le GL_2(F)$ there is a finite set $B$ of functions such that every $U$-right-invariant element of the span of the right translates of $w_{2,\mathrm{base}}$ lies in the span of $B$; and the central character condition (`hcentral`) $w_{2,\mathrm{base}}(z\cdot g) = \theta_0(z)\, w_{2,\mathrm{base}}(g)$ for scalar matrices $z \in F^{\times}$. Two Weyl elements are fixed: $w_{0,p}$ with matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ (`hw₀p`) and $w_J$ with matrix $\begin{pmatrix}0&1\\-1&0\end{pmatrix}$ (`hwJ`).
--
--   *Torus zeta hypotheses.* Constants $E : \mathrm{Fin}\,3 \to \mathbb{C}$ and $e : \mathrm{Fin}\,3 \to \mathbb{Z}$ are given, and three parallel hypotheses `hfe0`, `hfe1`, `hfe2` (one for each index $i = 0,1,2$) are imposed. Each asserts that for every $w$ in the span of the right translates of $w_{2,\mathrm{base}}$ there exist polynomials $P, P_d \in \mathbb{C}[X]$, integers $m, m_d$ and abscissae $\sigma_0, \sigma_1 \in \mathbb{R}$ such that, with respect to the multiplicative measure on $F^{\times}$ obtained by pulling back `mulMeasure (selfDualHaarAt ℚ p)` along $F^{\times} \to F$: for $\operatorname{Re} s > \sigma_0$ the function $y \mapsto w(\mathrm{diag}(y,1))\,\lambda_i(y)\,|y|^{s-1/2}$ is integrable with integral $q^{ms} P(q^{-s})$; for $\operatorname{Re} s < \sigma_1$ the function $y \mapsto w(\mathrm{diag}(y,1)\,w_J)\,\lambda_i(y)^{-1}\theta_0(y)^{-1}|y|^{1/2-s}$ is integrable with integral $q^{m_d s} P_d(q^{-s})$; and for all $s \in \mathbb{C}$ the monomial functional equation
--   $$q^{m_d s} P_d(q^{-s}) = \bigl(E_i\, q^{e_i s}\bigr)\,\bigl(q^{m s} P(q^{-s})\bigr)$$
--   holds. Here $|\cdot| =$ `modulus` is the module of $F$ and `diagOne y` $= \mathrm{diag}(y,1)$.
--
--   *Conclusion.* Equip $GL_2(F)$ with its Borel structure `localGLBorel ℚ p`. Then for every Haar measure $\mu_2$ on $GL_2(F)$, every Haar measure $\mu_{N_2}$ on the range $N_2$ of `unipotentGL2Hom`, the group of matrices $\begin{pmatrix}1&x\\0&1\end{pmatrix}$, and every $w_2$ in the span of the right translates of $w_{2,\mathrm{base}}$, both of the following hold, the integrals being taken against $\mu_2$ weighted by the density [`HaarQuotient.density N₂ μN₂`](def/HaarQuotient.html#L25).
--
--   First, there exist $m \in \mathbb{Z}$, $P \in \mathbb{C}[X]$ and $\sigma_2 \in \mathbb{R}$ such that for every $s$ with $\operatorname{Re} s > \sigma_2$ the function
--   $$g \mapsto \bigl(W_3(\iota g)\, w_2(g)\bigr)\,|\det g|^{s-1/2}$$
--   is integrable against that weighted measure, where $\iota =$ `iotaGL` is the block embedding $h \mapsto \mathrm{diag}(h,1)$ of $GL_2$ into $GL_3$, and
--   $$\Psi\bigl(s; W_3 \circ \iota,\, w_2\bigr)\cdot\bigl(1 - \theta_0(\varpi)\lambda_1(\varpi)\lambda_2(\varpi)\, q^{-2s}\bigr) = q^{ms} P(q^{-s}),$$
--   where $\Psi$ denotes [`RSCarrier.rsLocalIntegral`](def/LanglandsTunnell_RSCarrier.html#L16) for $\mu_2$, $N_2$, $\mu_{N_2}$ and the modulus function $g \mapsto |\det g|$, that is, the integral of the displayed integrand.
--
--   Second, there exist $m_d \in \mathbb{Z}$, $P_d \in \mathbb{C}[X]$ and $\sigma_3 \in \mathbb{R}$ such that for every $s$ with $\operatorname{Re} s > \sigma_3$ the function
--   $$g \mapsto \Bigl(\widetilde{W_3}(\iota g)\cdot \bigl(|\det g|\, w_2\bigl(w_{0,p}\cdot {}^{t}g^{-1}\bigr)\bigr)\Bigr)\,|\det g|^{s-1/2}$$
--   is integrable against the same weighted measure, where $\widetilde{W_3} =$ `dualWhittakerFn3 W₃` is $h \mapsto W_3(w_\ell \cdot {}^{t}h^{-1})$ with $w_\ell =$ `longWeyl3` the $3\times 3$ antidiagonal permutation matrix, ${}^{t}h^{-1} =$ `transposeInv3 h`, and ${}^{t}g^{-1} =$ `transposeInvN (Fin 2) g`, and
--   $$\Psi\bigl(s; \widetilde{W_3} \circ \iota,\, g \mapsto |\det g|\,w_2(w_{0,p}\,{}^{t}g^{-1})\bigr)\cdot\Bigl(1 - \bigl(\theta_0(\varpi)\lambda_1(\varpi)\lambda_2(\varpi)\bigr)^{-1} q^{-2}\, q^{-2s}\Bigr) = q^{m_d s} P_d(q^{-s}).$$
--
--   Thus each of the two local Rankin–Selberg integrals, once multiplied by the indicated central Tate factor, is a monomial $q^{ms}$ times a polynomial in $q^{-s}$ on a right half-plane.
--
--   This is the local rationality statement of Jacquet–Piatetski-Shapiro–Shalika theory for a $GL_3 \times GL_2$ pair at a finite place, in the form where the $GL_3$ vector is a translated Jacquet–Whittaker function of a principal series in the chamber $\sigma_2 < \sigma_1 < \sigma_0$ and the central Tate factor arising from the unfolding has been cleared, leaving a Laurent-polynomial expression in $q^{-s}$ for both the integral and its dual. It feeds the corresponding statement for families of twists, [`LanglandsTunnell.RankinSelberg.exists_forall_lt_rsLocalIntegral_jacquetWhittaker3_twistFamily_mul_centralTate_eq_cpow_mul_eval`](thm.html#LanglandsTunnell.RankinSelberg.exists_forall_lt_rsLocalIntegral_jacquetWhittaker3_twistFamily_mul_centralTate_eq_cpow_mul_eval), in the converse-theorem input to the Langlands–Tunnell step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_rsLocalIntegral_jacquetWhittaker3_mul_centralTate_eq_cpow_mul_eval_and_dual_of_chamber.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral_jacquetWhittaker3_mul_centralTate_eq_cpow_mul_eval_and_dual_of_chamber
    (p : HeightOneSpectrum (𝓞 ℚ))

    (ϖ : (p.adicCompletion ℚ)ˣ) (hϖ : Valued.v (ϖ : p.adicCompletion ℚ) = WithZero.exp (-1 : ℤ))

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
          (μN₂ : Measure ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range) [μN₂.IsHaarMeasure],
        ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∃ (m : ℤ) (P : Polynomial ℂ) (σ₂ : ℝ), ∀ s : ℂ, σ₂ < s.re →
            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (W₃ (iotaGL g) * w₂ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)) ∧
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂
                  (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ))
                  s (fun g => W₃ (iotaGL g)) w₂ *
                (1 - ((θ₀ ϖ : ℂˣ) : ℂ) * ((lam 1 ϖ : ℂˣ) : ℂ) * ((lam 2 ϖ : ℂˣ) : ℂ) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(2 : ℂ) * s)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
          (∃ (md : ℤ) (Pd : Polynomial ℂ) (σ₃ : ℝ), ∀ s : ℂ, σ₃ < s.re →
            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (dualWhittakerFn3 W₃ (iotaGL g) * (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)) ∧
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂
                  (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ))
                  s (fun g => dualWhittakerFn3 W₃ (iotaGL g)) (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) *
                (1 - (((θ₀ ϖ : ℂˣ) : ℂ) * ((lam 1 ϖ : ℂˣ) : ℂ) * ((lam 2 ϖ : ℂˣ) : ℂ))⁻¹ * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(2 : ℂ)) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(2 : ℂ) * s)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) := by sorry
