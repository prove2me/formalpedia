-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_rsLocalIntegral22_dual_mul_one_sub_eq_cpow_mul_eval_of_principalSeries2_of_forall_torusZeta_polynomial
-- name    : LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral22_dual_mul_one_sub_eq_cpow_mul_eval_of_principalSeries2_of_forall_torusZeta_polynomial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/f25360e1-c516-5266-bf66-6965b38c2999
-- title:
--   Rationality of the dual GL₂× GL₂ Rankin–Selberg integral
-- statement:
--   Let $p$ be a nonzero prime ideal of $\mathcal{O}_{\mathbb{Q}}$, write $F$ for the completion `p.adicCompletion ℚ`, $\psi =$ [`NumberField.StandardAddChar.psiLocal ℚ p`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65) for the standard local additive character, $dx$ for the self-dual measure `selfDualHaarAt ℚ p`, and $\mathrm{N}p$ for `Ideal.absNorm p.asIdeal`. Throughout, $|\cdot|$ denotes `modulus`, which on $F$ agrees with the norm.
--
--   Uniformiser data. An element $\varpi$ of the valuation ring of $F$ is given whose image in $F$ is nonzero (`hπ`) and has valuation $\exp(-1)$ (`hϖ`).
--
--   Principal-series data. A pair of characters $\mu_0,\mu_1 : F^\times \to \mathbb{C}^\times$ is given, each locally constant (`hμ`), together with real exponents $\sigma_0,\sigma_1$ such that $\|\mu_i(a)\| = \|a\|^{\sigma_i}$ (`hσ`) and $\sigma_1 < \sigma_0$ (`h01`); and a function $\varphi : GL_2(F)\to\mathbb{C}$ lying in `principalSeries2 p μ` (`hφ`), i.e. $\varphi$ is locally constant, invariant under left translation by the upper unipotent matrices $\begin{pmatrix}1&x\\0&1\end{pmatrix}$, and satisfies $\varphi(\mathrm{diag}(a_0,a_1)g) = \mu_0(a_0)\mu_1(a_1)\sqrt{\|a_0\|/\|a_1\|}\,\varphi(g)$.
--
--   Test-function datum. A function $\Phi_2 : F\times F\to\mathbb{C}$ is given which is locally constant and of compact support (`hΦ₂`).
--
--   Whittaker data. A character $\theta_0 : F^\times\to\mathbb{C}^\times$, a nonzero ideal $N$ of $\mathcal{O}_{\mathbb{Q}}$ (`hN`) and a function $w_{2,\mathrm{base}} : GL_2(F)\to\mathbb{C}$ are given subject to: the Whittaker transformation law $w_{2,\mathrm{base}}(\begin{pmatrix}1&x\\0&1\end{pmatrix}g) = \psi(x)\,w_{2,\mathrm{base}}(g)$ (`hw₂law`); right invariance under the compact open subgroup [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N`](def/AdelicDock_LocalEmbedding.html#L178), the preimage under the local embedding of the finite-adelic level-$N$ level-one subgroup (`hw₂K`); nonvanishing, $w_{2,\mathrm{base}}\neq 0$ (`hw₂ne`); irreducibility of the right-translation module, namely that every nonzero $w$ in the $\mathbb{C}$-span $V$ of the right translates $g\mapsto w_{2,\mathrm{base}}(gh)$ has $w_{2,\mathrm{base}}$ in the span of its own right translates (`hw₂irr`); admissibility, namely that for every open subgroup $U\le GL_2(F)$ there is a finite family $B$ of functions such that every $w\in V$ which is right $U$-invariant lies in the span of $B$ (`hw₂adm`); and the central character law $w_{2,\mathrm{base}}(z\cdot 1_2\, g) = \theta_0(z)\,w_{2,\mathrm{base}}(g)$ for $z\in F^\times$ (`hcentral`).
--
--   Weyl elements. Elements $w_{0,p}$ and $w_J$ of $GL_2(F)$ are given with underlying matrices $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ (`hw₀p`) and $\begin{pmatrix}0&1\\-1&0\end{pmatrix}$ (`hwJ`).
--
--   Torus zeta hypotheses. Constants $E_0,E_1\in\mathbb{C}$ and integers $e_0,e_1$ are given, and for $i=0$ (`hfe0`) and $i=1$ (`hfe1`) it is assumed that for every $w\in V$ there exist polynomials $P,P^\vee\in\mathbb{C}[X]$, integers $m,m^\vee$ and reals $\sigma_0',\sigma_1'$ with five clauses: for $\mathrm{Re}\,s > \sigma_0'$ the function $y\mapsto w(\mathrm{diag}(y,1))\,\mu_i(y)\,|y|^{s-1/2}$ is integrable for the multiplicative measure `Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))` on $F^\times$, and its integral equals $\mathrm{N}p^{\,m s}P(\mathrm{N}p^{-s})$; for $\mathrm{Re}\,s < \sigma_1'$ the function $y\mapsto w(\mathrm{diag}(y,1)\,w_J)\,\mu_i(y)^{-1}\theta_0(y)^{-1}|y|^{1/2-s}$ is integrable for the same measure, and its integral equals $\mathrm{N}p^{\,m^\vee s}P^\vee(\mathrm{N}p^{-s})$; and the monomial functional equation $\mathrm{N}p^{\,m^\vee s}P^\vee(\mathrm{N}p^{-s}) = \bigl(E_i\,\mathrm{N}p^{\,e_i s}\bigr)\bigl(\mathrm{N}p^{\,m s}P(\mathrm{N}p^{-s})\bigr)$ holds for all $s\in\mathbb{C}$.
--
--   Conclusion. Equip $GL_2(F)$ and $F$ with the Borel measurable structures `localGLBorel ℚ p` and `localBorel ℚ p`. Let $N_2$ denote the range of `unipotentGL2Hom` over $F$, the group of matrices $\begin{pmatrix}1&x\\0&1\end{pmatrix}$. Then for every Haar measure $\mu_2$ on $GL_2(F)$, every Haar measure $\mu_{N_2}$ on $N_2$, and every $w_2\in V$, there exist an integer $m$, a polynomial $P\in\mathbb{C}[X]$ and a real $\sigma_3$ such that for all $s$ with $\sigma_3 < \mathrm{Re}\,s$ both of the following hold, where
--   $$W'(g) = \int_F \psi(x)\,\varphi\Bigl(\begin{pmatrix}0&1\\1&0\end{pmatrix}\begin{pmatrix}1&x\\0&1\end{pmatrix}\bigl(w_{0,p}\,{}^t g^{-1}\bigr)\Bigr)\,dx,$$
--   $$\mathcal{F}(g) = |\det g|\;w_2\bigl(w_{0,p}\,{}^t g^{-1}\bigr)\int_{F\times F}\Phi_2(u)\,\psi\bigl(u_1 g_{10} + u_2 g_{11}\bigr)\,du,$$
--   with ${}^t g^{-1}$ the transpose-inverse `transposeInvN (Fin 2) g` and $du$ the product of two copies of $dx$:
--
--   first, the function $g\mapsto \bigl(W'(g)\,\mathcal{F}(g)\bigr)\,|\det g|^{(s+1/2)-1/2}$ is integrable for the measure $\mu_2$ weighted by the density [`HaarQuotient.density`](def/HaarQuotient.html#L25) attached to $N_2$ and $\mu_{N_2}$;
--
--   second, the value of [`RSCarrier.rsLocalIntegral`](def/LanglandsTunnell_RSCarrier.html#L16) for the data $\mu_2$, $N_2$, $\mu_{N_2}$, modulus-of-determinant $g\mapsto|\det g|$, spectral parameter $s+\tfrac12$, and the pair of functions $W'$ and $\mathcal{F}$ — that is, the integral of $\bigl(W'(g)\mathcal{F}(g)\bigr)|\det g|^{(s+1/2)-1/2}$ against the same weighted measure — satisfies
--   $$\Bigl(\text{that integral}\Bigr)\cdot\Bigl(1 - \bigl(\theta_0(\varpi)\mu_0(\varpi)\mu_1(\varpi)\bigr)^{-1}\,\mathrm{N}p^{-2}\,\mathrm{N}p^{-2s}\Bigr) = \mathrm{N}p^{\,m s}\,P\bigl(\mathrm{N}p^{-s}\bigr),$$
--   where $\varpi$ is understood as the unit of $F$ determined by its nonzero image. Thus after clearing the single dual central Tate factor the integral is a Laurent-monomial multiple of a polynomial in $\mathrm{N}p^{-s}$; the data $m$, $P$ and $\sigma_3$ may depend on $\mu_2$, $\mu_{N_2}$ and $w_2$.
--
--   This is the rationality statement for the dual local $GL_2\times GL_2$ Rankin–Selberg integral at a finite place: the integral over $N_2\backslash GL_2(F)$ of a principal-series Jacquet–Whittaker function against a Whittaker vector of an irreducible admissible generic representation with central character $\theta_0$, twisted by the Fourier transform of a locally constant compactly supported $\Phi_2$, becomes a Laurent polynomial in $\mathrm{N}p^{-s}$ once the dual central factor $1-(\theta_0\mu_0\mu_1)(\varpi)^{-1}\mathrm{N}p^{-2-2s}$ is cleared. It is the dual counterpart of the corresponding statement for the primal $(2,2)$ integral and feeds the assembly of the cleared local functional equation used in the converse-theorem input to the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_rsLocalIntegral22_dual_mul_one_sub_eq_cpow_mul_eval_of_principalSeries2_of_forall_torusZeta_polynomial.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_rsLocalIntegral22_dual_mul_one_sub_eq_cpow_mul_eval_of_principalSeries2_of_forall_torusZeta_polynomial
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
          ∃ (m : ℤ) (P : Polynomial ℂ) (σ₃ : ℝ), ∀ s : ℂ, σ₃ < s.re →
            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                ((fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                    φ (antidiagonal2 p * upperUnipotent2 p x * (w₀p * transposeInvN (Fin 2) g)) ∂(selfDualHaarAt ℚ p)) g * (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g) *
                    (∫ u : p.adicCompletion ℚ × p.adicCompletion ℚ, Φ₂ u *
                      NumberField.StandardAddChar.psiLocal ℚ p
                        (u.1 * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 + u.2 * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)
                    ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)))) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2 - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) ∧
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
                (1 - ((((θ₀ (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) * ((μ 0 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ) *
                      ((μ 1 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)))⁻¹ * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(2 : ℂ)) *
                    (Ideal.absNorm p.asIdeal : ℂ) ^ (-(2 : ℂ) * s)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) := by sorry
