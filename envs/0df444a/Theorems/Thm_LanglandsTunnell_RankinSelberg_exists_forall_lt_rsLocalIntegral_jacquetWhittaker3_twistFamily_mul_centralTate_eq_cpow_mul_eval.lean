-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_lt_rsLocalIntegral_jacquetWhittaker3_twistFamily_mul_centralTate_eq_cpow_mul_eval
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_lt_rsLocalIntegral_jacquetWhittaker3_twistFamily_mul_centralTate_eq_cpow_mul_eval
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/362c74a5-21c0-514a-b93f-dd32a56917a1
-- title:
--   Cleared local GL₃× GL₂ integrals along a flat twist family
-- statement:
--   Throughout, $p$ is a point of the height-one spectrum of the ring of integers of $\mathbb{Q}$, $F = \mathbb{Q}_p$ denotes the completion `p.adicCompletion ℚ`, and $q =$ `Ideal.absNorm p.asIdeal` is the residue cardinality; `modulus` is the module of an element of $F$ (equal to its norm), and $F$ and $GL_2(F)$, $GL_3(F)$ carry their Borel $\sigma$-algebras (`localBorel`, `localGLBorel`, with the associated `BorelSpace` instance).
--
--   Data on the $GL_3$ side. A triple $\lambda = (\lambda_0,\lambda_1,\lambda_2)$ of monoid homomorphisms $F^\times \to \mathbb{C}^\times$, each locally constant (`hlam`); a function $\Phi$ on $F^3$ which is locally constant and has compact support (`hΦ`); elements $x,y,z \in F$. A family `lamU` assigning to each $u \in \mathbb{C}$ a triple of characters, with `hlamU0` saying that the value at $u = 0$ is $\lambda$, and `hlamU` prescribing the values for all $u$ and all $a \in F^\times$: the zeroth component is $\lambda_0(a)\,\|a\|^{u}$, the first is $\lambda_1(a)$, and the second is $\lambda_2(a)\,\|a\|^{-u}$; thus `lamU u` is the flat deformation $(\lambda_0|\cdot|^{u},\lambda_1,\lambda_2|\cdot|^{-u})$.
--
--   For a triple $\chi$ of characters, `jacquetWhittaker3 p χ Φ` is the Whittaker function on $GL_3(F)$ obtained by applying `jacquetValue` to the right translate by $g$ of the big-cell section $h \mapsto$ `cellValue` $(\chi,h)\cdot\Phi(\,$`cellRatio` $h)$ supported on `bigCell3`. The translated function used below is $h \mapsto$ `jacquetWhittaker3` $p$ (`lamU` $u$) $\Phi$ of $\mathrm{diag}(1,-1,1)\cdot h\cdot(n(x,y,z)\,w)$, where $n(x,y,z)$ is the upper unipotent matrix with entries $x$, $y$, $z$ above the diagonal (`upperUnipotent3`) and $w$ is the antidiagonal permutation matrix `antidiagonal3`; `iotaGL` is the embedding $GL_2(F) \to GL_3(F)$, $g \mapsto \mathrm{diag}(g,1)$, and `dualWhittakerFn3` $W$ is $g \mapsto W(\,$`longWeyl3`$\cdot (g^{-1})^{\mathsf T})$.
--
--   Data on the $GL_2$ side. A monoid homomorphism $\theta_0 : F^\times \to \mathbb{C}^\times$; a nonzero ideal $N$ of the ring of integers of $\mathbb{Q}$ (`hN`); a function $w_{2,\mathrm{base}} : GL_2(F) \to \mathbb{C}$ subject to: `hw₂law`, the Whittaker transformation law $w_{2,\mathrm{base}}(u(t)g) = \psi_p(t)\,w_{2,\mathrm{base}}(g)$ for the standard local additive character $\psi_p =$ `psiLocal ℚ p` and $u(t) = \begin{pmatrix}1&t\\0&1\end{pmatrix}$; `hw₂K`, right invariance under the subgroup [`AdelicDock.localLevelOne`](def/AdelicDock_LocalEmbedding.html#L178) of level $N$ at $p$ (the pullback along the local embedding into $GL_2$ of the finite adeles of the level-one subgroup of level $N$); `hw₂ne`, $w_{2,\mathrm{base}} \neq 0$; `hw₂irr`, irreducibility of the span $V$ of the right translates $g \mapsto w_{2,\mathrm{base}}(gh)$, in the form that every nonzero $w \in V$ has $w_{2,\mathrm{base}}$ in the span of its own right translates; `hw₂adm`, admissibility, namely for every open subgroup $U \le GL_2(F)$ there is a finite set $B$ of functions such that every $w \in V$ invariant under right translation by $U$ lies in the span of $B$; and `hcentral`, $w_{2,\mathrm{base}}(z\cdot g) = \theta_0(z)\,w_{2,\mathrm{base}}(g)$ for scalar matrices $z \in F^\times$. Further, $w_{0,p}$ and $w_J$ are elements of $GL_2(F)$ with underlying matrices $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and $\begin{pmatrix}0&1\\-1&0\end{pmatrix}$ respectively (`hw₀p`, `hwJ`).
--
--   Torus zeta hypotheses. Constants $E : \mathrm{Fin}\,3 \to \mathbb{C}$ and $e : \mathrm{Fin}\,3 \to \mathbb{Z}$ are given, and for each index $i \in \{0,1,2\}$ the hypothesis `hfe0`, `hfe1`, `hfe2` asserts: for every $w \in V$ there are polynomials $P, P^{\vee} \in \mathbb{C}[X]$, integers $m, m^{\vee}$ and reals $\sigma_0, \sigma_1$ such that (i) for $\operatorname{Re} s > \sigma_0$ the function $y \mapsto w(\mathrm{diag}(y,1))\,\lambda_i(y)\,|y|^{s-1/2}$ is integrable on $F^\times$ for the measure obtained by pulling back along $F^\times \hookrightarrow F$ the multiplicative measure `mulMeasure` of the self-dual additive Haar measure `selfDualHaarAt ℚ p`, (ii) for those $s$ the corresponding integral equals $q^{ms}P(q^{-s})$, (iii) for $\operatorname{Re} s < \sigma_1$ the function $y \mapsto w(\mathrm{diag}(y,1)\,w_J)\,\lambda_i(y)^{-1}\theta_0(y)^{-1}|y|^{1/2-s}$ is integrable for the same measure, (iv) for those $s$ that integral equals $q^{m^{\vee}s}P^{\vee}(q^{-s})$, and (v) for all $s \in \mathbb{C}$ the monomial functional equation $q^{m^{\vee}s}P^{\vee}(q^{-s}) = E_i\,q^{e_i s}\cdot q^{ms}P(q^{-s})$ holds.
--
--   Conclusion. For every Haar measure $\mu_2$ on $GL_2(F)$, every Haar measure $\mu_{N_2}$ on the range of `unipotentGL2Hom` (the image of the additive group of $F$ under $t \mapsto \begin{pmatrix}1&t\\0&1\end{pmatrix}$), and every $w_2 \in V$, there exist $c, c^{\vee} \in \mathbb{C}$ and $u_1 \in \mathbb{R}$ with the following property: for every real $u > u_1$ there are polynomials $P, P^{\vee} \in \mathbb{C}[X]$, integers $m, m^{\vee}$ and reals $\sigma_2, \sigma_3$ such that, writing $W_u(h) =$ `jacquetWhittaker3` $p$ (`lamU` $u$) $\Phi\,(\mathrm{diag}(1,-1,1)\cdot h\cdot(n(x,y,z)w))$ and $\nu = \mu_2$ weighted by the density [`HaarQuotient.density`](def/HaarQuotient.html#L25) of the unipotent subgroup relative to $\mu_{N_2}$:
--
--   (1) for $\operatorname{Re} s > \sigma_2$ the function $g \mapsto W_u(\iota(g))\,w_2(g)\,|\det g|^{s-1/2}$ on $GL_2(F)$, with $\iota =$ `iotaGL`, is $\nu$-integrable;
--
--   (2) for $\operatorname{Re} s > \sigma_3$ the function $g \mapsto \big(\,$`dualWhittakerFn3` $W_u\big)(\iota(g))\cdot |\det g|\cdot w_2\big(w_{0,p}\cdot (g^{-1})^{\mathsf T}\big)\cdot|\det g|^{s-1/2}$ is $\nu$-integrable;
--
--   (3) for $\operatorname{Re} s > \sigma_2$, the local Rankin–Selberg integral [`RSCarrier.rsLocalIntegral`](def/LanglandsTunnell_RSCarrier.html#L16) $\mu_2$, the unipotent subgroup, $\mu_{N_2}$, the modulus function $g \mapsto |\det g|$, at $s$, of the pair $(W_u \circ \iota,\; w_2)$ — that is, $\int W_u(\iota(g))\,w_2(g)\,|\det g|^{s-1/2}\,d\nu(g)$ — multiplied by the two-term clearing sum indexed by the finite set $\{(0,0),(2,-1)\} \subset \mathbb{Z}^2$, whose terms are $q^{-a s}q^{-b u}$ with coefficient $1$ at $(a,b) = (0,0)$ and $-c$ otherwise, i.e. by $1 - c\,q^{-2s}q^{u}$, equals $q^{ms}P(q^{-s})$;
--
--   (4) for $\operatorname{Re} s > \sigma_3$, the same local Rankin–Selberg integral taken with $W = \big($`dualWhittakerFn3` $W_u\big)\circ \iota$ and $F(g) = |\det g|\,w_2\big(w_{0,p}(g^{-1})^{\mathsf T}\big)$, multiplied by the clearing sum indexed by $\{(0,0),(2,1)\}$ with coefficient $1$ at $(0,0)$ and $-c^{\vee}$ otherwise, i.e. by $1 - c^{\vee}q^{-2s}q^{-u}$, equals $q^{m^{\vee}s}P^{\vee}(q^{-s})$.
--
--   Thus the constants $c, c^{\vee}$ and the threshold $u_1$ are uniform in $u$, while the polynomials, the integer exponents and the abscissae of convergence are allowed to depend on $u$.
--
--   This is the local $GL_3 \times GL_2$ Rankin–Selberg statement at the finite place $p$: in the chamber $u \gg 0$ of the flat twist family $(\lambda_0|\cdot|^{u},\lambda_1,\lambda_2|\cdot|^{-u})$ the integral, after multiplication by an explicit two-variable clearing factor $1 - c\,q^{-2s}q^{\pm u}$, is a Laurent polynomial in $q^{-s}$, and likewise for the dual integral. It feeds the descent of the cleared functional equation to the centre of the family in [`LanglandsTunnell.RankinSelberg.forall_rsLocalIntegral_clearedFE_prod_of_jacquetWhittaker3_of_forall_torusZeta_fe_core`](thm.html#LanglandsTunnell.RankinSelberg.forall_rsLocalIntegral_clearedFE_prod_of_jacquetWhittaker3_of_forall_torusZeta_fe_core).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_lt_rsLocalIntegral_jacquetWhittaker3_twistFamily_mul_centralTate_eq_cpow_mul_eval.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_forall_lt_rsLocalIntegral_jacquetWhittaker3_twistFamily_mul_centralTate_eq_cpow_mul_eval
    (p : HeightOneSpectrum (𝓞 ℚ))

    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i))
    (Φ : (Fin 3 → p.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (x y z : p.adicCompletion ℚ)

    (lamU : ℂ → Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (hlamU0 : lamU 0 = lam)
    (hlamU : ∀ (u : ℂ) (a : (p.adicCompletion ℚ)ˣ),
      ((lamU u 0 a : ℂˣ) : ℂ) = ((lam 0 a : ℂˣ) : ℂ) * ((‖(a : p.adicCompletion ℚ)‖ : ℂ)) ^ u ∧
        ((lamU u 1 a : ℂˣ) : ℂ) = ((lam 1 a : ℂˣ) : ℂ) ∧
          ((lamU u 2 a : ℂˣ) : ℂ) = ((lam 2 a : ℂˣ) : ℂ) * ((‖(a : p.adicCompletion ℚ)‖ : ℂ)) ^ (-u))

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
          ∃ (c cd : ℂ) (u₁ : ℝ), ∀ u : ℝ, u₁ < u → ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ),
            (∀ s : ℂ, σ₂ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (jacquetWhittaker3 p (lamU u) Φ (diagonal3 p ![1, -1, 1] * iotaGL g * (upperUnipotent3 x y z * antidiagonal3 p)) * w₂ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂))) ∧
            (∀ s : ℂ, σ₃ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (dualWhittakerFn3 (fun h => jacquetWhittaker3 p (lamU u) Φ (diagonal3 p ![1, -1, 1] * h * (upperUnipotent3 x y z * antidiagonal3 p))) (iotaGL g) * (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)) (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂))) ∧
            (∀ s : ℂ, σ₂ < s.re →
              RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂
                  (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ))
                  s (fun g => jacquetWhittaker3 p (lamU u) Φ (diagonal3 p ![1, -1, 1] * iotaGL g * (upperUnipotent3 x y z * antidiagonal3 p))) w₂ *
                (∑ ab ∈ ({((0 : ℤ), (0 : ℤ)), (2, -1)} : Finset (ℤ × ℤ)),
                  (fun ab : ℤ × ℤ => if ab = (0, 0) then (1 : ℂ) else -c) ab *
                    (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.1 : ℂ) * s) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.2 : ℂ) * (u : ℂ))) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
            (∀ s : ℂ, σ₃ < s.re →
              RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂
                  (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ))
                  s (fun g => dualWhittakerFn3 (fun h => jacquetWhittaker3 p (lamU u) Φ (diagonal3 p ![1, -1, 1] * h * (upperUnipotent3 x y z * antidiagonal3 p))) (iotaGL g)) (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) *
                (∑ ab ∈ ({((0 : ℤ), (0 : ℤ)), (2, 1)} : Finset (ℤ × ℤ)),
                  (fun ab : ℤ × ℤ => if ab = (0, 0) then (1 : ℂ) else -cd) ab *
                    (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.1 : ℂ) * s) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.2 : ℂ) * (u : ℂ))) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) := by sorry
