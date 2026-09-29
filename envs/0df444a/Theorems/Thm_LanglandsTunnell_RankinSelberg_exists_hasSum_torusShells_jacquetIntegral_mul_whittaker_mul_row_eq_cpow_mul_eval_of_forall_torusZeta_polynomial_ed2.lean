-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_hasSum_torusShells_jacquetIntegral_mul_whittaker_mul_row_eq_cpow_mul_eval_of_forall_torusZeta_polynomial_ed2
-- name    : LanglandsTunnell.RankinSelberg.exists_hasSum_torusShells_jacquetIntegral_mul_whittaker_mul_row_eq_cpow_mul_eval_of_forall_torusZeta_polynomial_ed2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/7f0965a8-c564-5da6-a349-b2e2e6926b95
-- title:
--   Torus-shell series of Jacquet and Whittaker integrals sums to q^{ms}P(q^{-s})
-- statement:
--   Throughout, $p$ is a height-one prime of the ring of integers of $\mathbb{Q}$, $F = \mathbb{Q}_p$ denotes the completion `p.adicCompletion ℚ`, and $q =$ `Ideal.absNorm p.asIdeal` is the residue cardinality. The element $\varpi \in F^{\times}$ is a unit of $F$ whose valuation is $\exp(-1)$ (hypothesis `hϖ`), i.e. a uniformiser.
--
--   The inducing data consist of two monoid homomorphisms $\mu_0,\mu_1 : F^{\times} \to \mathbb{C}^{\times}$, each locally constant (`hμ`), together with real exponents $\sigma_0,\sigma_1$ such that $\|\mu_i(a)\| = \|a\|^{\sigma_i}$ for every unit $a$ (`hσ`), subject to the chamber condition $\sigma_1 < \sigma_0$ (`h01`). The function $\varphi : \mathrm{GL}_2(F) \to \mathbb{C}$ lies in `principalSeries2 p μ`, that is: $\varphi$ is locally constant, $\varphi(n(x)g) = \varphi(g)$ for the upper unipotent $n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$ and all $g$, and $\varphi(\mathrm{diag}(a_0,a_1)g) = \mathrm{torusChar2}(a)\,\mathrm{halfModulus2}(a)\,\varphi(g)$ for all diagonal $\mathrm{diag}(a_0,a_1)$ with unit entries.
--
--   A further function $\Phi_2 : F \times F \to \mathbb{C}$ is given, assumed locally constant and of compact support (`hΦ₂`); $\Phi_2$ does not occur in the conclusion.
--
--   The Whittaker data consist of a monoid homomorphism $\theta_0 : F^{\times} \to \mathbb{C}^{\times}$, a nonzero ideal $N$ of the ring of integers of $\mathbb{Q}$ (`hN`), and a function $w_2^{\flat} : \mathrm{GL}_2(F) \to \mathbb{C}$ subject to five hypotheses: `hw₂law`, the Whittaker transformation law $w_2^{\flat}(n(x)g) = \psi_p(x)\,w_2^{\flat}(g)$ for the standard additive character `psiLocal ℚ p` at $p$; `hw₂K`, right invariance under the level subgroup [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N`](def/AdelicDock_LocalEmbedding.html#L178), the pullback along the local embedding $\mathrm{GL}_2(F) \to \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}}^{\mathrm{fin}})$ of the finite level-$N$ subgroup; `hw₂ne`, $w_2^{\flat} \neq 0$; `hw₂irr`, an irreducibility clause stating that for every $w$ in the $\mathbb{C}$-span $V$ of the right translates $g \mapsto w_2^{\flat}(gh)$ of $w_2^{\flat}$ with $w \neq 0$, the function $w_2^{\flat}$ itself lies in the span of the right translates of $w$; and `hw₂adm`, an admissibility clause stating that for every open subgroup $U \le \mathrm{GL}_2(F)$ there is a finite set $B$ of functions such that every $w \in V$ which is right $U$-invariant lies in the span of $B$. Finally `hcentral` asserts the central character law $w_2^{\flat}(z \cdot g) = \theta_0(z)\,w_2^{\flat}(g)$ for scalar matrices $z \in F^{\times}$.
--
--   The element $w_J \in \mathrm{GL}_2(F)$ is required to have matrix $\begin{pmatrix}0&1\\-1&0\end{pmatrix}$ (`hwJ`).
--
--   Two families of local functional equations are assumed, indexed by $i = 0$ (`hfe0`) and $i = 1$ (`hfe1`), with prescribed factors $E : \mathrm{Fin}\,2 \to \mathbb{C}$ and $e : \mathrm{Fin}\,2 \to \mathbb{Z}$. For each $i$ the hypothesis states: for every $w \in V$ there exist polynomials $P, P^{\vee} \in \mathbb{C}[X]$, integers $m, m^{\vee}$ and reals $\sigma_0', \sigma_1'$ such that (a) for $\mathrm{Re}\,s > \sigma_0'$ the function $y \mapsto w(\mathrm{diag}(y,1))\,\mu_i(y)\,|y|^{\,s-1/2}$ is integrable on $F^{\times}$ against the multiplicative measure obtained by pulling back along $y \mapsto y$ the measure $dx/|x|$ formed from the self-dual additive Haar measure `selfDualHaarAt ℚ p` (here $|{\cdot}|$ is the module `modulus`), and (b) its integral equals $q^{\,m s}\,P(q^{-s})$; (c) for $\mathrm{Re}\,s < \sigma_1'$ the dual integrand $y \mapsto w(\mathrm{diag}(y,1)\,w_J)\,\mu_i(y)^{-1}\theta_0(y)^{-1}|y|^{\,1/2-s}$ is integrable for the same measure, and (d) its integral equals $q^{\,m^{\vee} s}\,P^{\vee}(q^{-s})$; and (e) for all $s \in \mathbb{C}$ the identity $q^{\,m^{\vee} s}P^{\vee}(q^{-s}) = \bigl(E_i\,q^{\,e_i s}\bigr)\bigl(q^{\,m s}P(q^{-s})\bigr)$ holds.
--
--   Lastly a locally constant weight $B : F \times F \to \mathbb{C}$ is given (`hB`).
--
--   Conclusion. With $\mathrm{GL}_2(F)$ and $F$ carrying their Borel $\sigma$-algebras, for every Haar measure $\mu_2$ on $\mathrm{GL}_2(F)$ and every $w_2 \in V$ there exist an integer $m$, a polynomial $P \in \mathbb{C}[X]$ and a real $\sigma_{\star}$ such that for every $s$ with $\sigma_{\star} < \mathrm{Re}\,s$ the family indexed by $d \in \mathbb{Z}$ whose $d$-th term is
--   $$q^{\,d}\,q^{-d s} \int_{K} \Bigl(\int_{F} \psi_p(x)\,\varphi\bigl(\begin{pmatrix}0&1\\1&0\end{pmatrix} n(x)\,(a_d k)\bigr)\,dx\Bigr)\; w_2(a_d k)\; B\bigl(k_{10}, k_{11}\bigr)\, d\mu_2(k)$$
--   is summable with sum $q^{\,m s}\,P(q^{-s})$ (`HasSum`, hence unconditional convergence). Here $a_d = \begin{pmatrix}\varpi^{d}&0\\0&1\end{pmatrix}$ is `diagZ` at the uniformiser $\varpi$, the inner integral is taken against `selfDualHaarAt ℚ p`, the outer integral is over the set $K =$ [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤`](def/AdelicDock_LocalEmbedding.html#L178) (the level subgroup at the unit ideal $\top$), and $(k_{10},k_{11})$ is the bottom row of the matrix of $k$.
--
--   This is the local Rankin–Selberg computation at the finite place $p$ in the deep-torus direction: the shell-by-shell series pairing the Jacquet integral of a principal-series vector in the chamber $\sigma_1 < \sigma_0$ against a vector of the Whittaker space generated by $w_2^{\flat}$, weighted by a locally constant function of the bottom row, sums to a Laurent polynomial $q^{ms}P(q^{-s})$ in $q^{-s}$ on a right half-plane. It feeds the assembly of the local integral `exists_rsLocalIntegral22_mul_one_sub_eq_cpow_mul_eval_of_principalSeries2_of_forall_torusZeta_polynomial_core` in the converse-theorem input to the Langlands–Tunnell step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_hasSum_torusShells_jacquetIntegral_mul_whittaker_mul_row_eq_cpow_mul_eval_of_forall_torusZeta_polynomial_ed2.lean

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

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.RankinSelberg
open MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

theorem LanglandsTunnell.RankinSelberg.exists_hasSum_torusShells_jacquetIntegral_mul_whittaker_mul_row_eq_cpow_mul_eval_of_forall_torusZeta_polynomial_ed2
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

    (B : p.adicCompletion ℚ × p.adicCompletion ℚ → ℂ) (hB : IsLocallyConstant B)
    :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
        ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          ∃ (m : ℤ) (P : Polynomial ℂ) (σs : ℝ), ∀ s : ℂ, σs < s.re →
            HasSum (fun d : ℤ =>
                (Ideal.absNorm p.asIdeal : ℂ) ^ d * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(d : ℂ) * s) *
                  ∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) :
                      Set (GL (Fin 2) (p.adicCompletion ℚ))),
                    (∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                        φ (antidiagonal2 p * upperUnipotent2 p x *
                          (diagZ (ϖ : p.adicCompletion ℚ) ϖ.ne_zero d * k)) ∂(selfDualHaarAt ℚ p)) *
                      w₂ (diagZ (ϖ : p.adicCompletion ℚ) ϖ.ne_zero d * k) *
                      B ((k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) ∂μ₂)
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) := by sorry
