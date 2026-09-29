-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_apply_diagOne_mul_weylJ_eq_of_apply_diagOne_eq_inv_mul_indicator_shell_of_cuspidal
-- name    : LanglandsTunnell.RankinSelberg.forall_apply_diagOne_mul_weylJ_eq_of_apply_diagOne_eq_inv_mul_indicator_shell_of_cuspidal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/eb2261c8-9c17-5b8f-9068-28dcbebd77e5
-- title:
--   One-shell Kirillov function under the Weyl element, cuspidal case
-- statement:
--   Let $p$ be a nonzero prime of $\mathcal O_{\mathbb Q}$, write $F=\mathbb Q_p$ for the completion $\hat{\mathbb Q}_p$ at $p$ and $q=\lvert\mathcal O_{\mathbb Q}/p\rvert$, let $\theta_0:F^\times\to\mathbb C^\times$ be a homomorphism, and let $N\neq 0$ be an ideal of $\mathcal O_{\mathbb Q}$. Let $w_{2,\mathrm{base}}:\mathrm{GL}_2(F)\to\mathbb C$ be nonzero and satisfy: the Whittaker law $w_{2,\mathrm{base}}\bigl(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}g\bigr)=\psi_p(x)w_{2,\mathrm{base}}(g)$ for the local component $\psi_p$ at $p$ of the standard adelic additive character; right invariance under [`AdelicDock.localLevelOne`](def/AdelicDock_LocalEmbedding.html#L178), the pullback along the local embedding $\mathrm{GL}_2(F)\to\mathrm{GL}_2(\mathbb A_{\mathbb Q}^{\mathrm{fin}})$ of the finite level-one subgroup of level $N$; the irreducibility condition that every nonzero element $w$ of the span $V$ of the right translates $g\mapsto w_{2,\mathrm{base}}(gh)$ has $w_{2,\mathrm{base}}$ in the span of the right translates of $w$; the admissibility condition that for every open subgroup $U\le\mathrm{GL}_2(F)$ some finite family spans the right $U$-invariant vectors of $V$; and $w_{2,\mathrm{base}}(z\cdot g)=\theta_0(z)w_{2,\mathrm{base}}(g)$ for scalar matrices. Let $w_J\in\mathrm{GL}_2(F)$ have matrix $\left(\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\right)$, let $\chi:F^\times\to\mathbb C^\times$ be a locally constant homomorphism, and let $E_0\in\mathbb C$, $e_0\in\mathbb Z$. Assume the torus functional equation `hfe`: for every $w\in V$ there are polynomials $P,P^\vee$, integers $m_1,m_1^\vee$ and reals $\sigma_0,\sigma_1$ such that for $\operatorname{Re}s>\sigma_0$ the function $y\mapsto w(\mathrm{diag}(y,1))\chi(y)\lvert y\rvert^{s-1/2}$ is integrable against the multiplicative measure on $F^\times$ obtained by restricting the self-dual additive Haar measure at $p$ to $F\setminus\{0\}$, weighting by $\mathrm{mod}(x)^{-1}$ and pulling back along $F^\times\to F$, with integral $q^{m_1 s}P(q^{-s})$; for $\operatorname{Re}s<\sigma_1$ the corresponding statement for $y\mapsto w(\mathrm{diag}(y,1)w_J)\chi(y)^{-1}\theta_0(y)^{-1}\lvert y\rvert^{1/2-s}$ with integral $q^{m_1^\vee s}P^\vee(q^{-s})$; and the identity $q^{m_1^\vee s}P^\vee(q^{-s})=E_0q^{e_0 s}\,q^{m_1 s}P(q^{-s})$ for all $s$. Assume also the cuspidality condition `hcusp`: every $v\in V$ vanishes at $\mathrm{diag}(y,1)$ for all $y$ with valuation below some bound. The conclusion: for every $m\in\mathbb Z$ and every $w_2\in V$ with $w_2(\mathrm{diag}(y,1))=\chi(y)^{-1}\mathbf 1[\lvert y\rvert=q^{-m}]$ for all $y\in F^\times$, one has $w_2(\mathrm{diag}(y,1)w_J)=E_0q^{e_0/2}\chi(y)\theta_0(y)\mathbf 1[\lvert y\rvert=q^{-(e_0-m)}]$ for all $y\in F^\times$, where the indicators are expressed through $\mathrm{Valued.v}(y)=\exp(-m)$, respectively $\exp(-(e_0-m))$.
--
--   This is the local Kirillov-model computation at a finite place: a vector whose restriction to the diagonal torus is the single-shell function $\chi^{-1}\mathbf 1[\lvert y\rvert=q^{-m}]$ has, after application of the Weyl element, the single-shell profile $E_0q^{e_0/2}\chi\theta_0\mathbf 1[\lvert y\rvert=q^{-(e_0-m)}]$ determined by the assumed functional equation. It feeds the Rankin–Selberg local integral and Godement-type zeta computations for cuspidal local components used in the converse-theorem input to Langlands–Tunnell.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_forall_apply_diagOne_mul_weylJ_eq_of_apply_diagOne_eq_inv_mul_indicator_shell_of_cuspidal.lean

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
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection

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

theorem LanglandsTunnell.RankinSelberg.forall_apply_diagOne_mul_weylJ_eq_of_apply_diagOne_eq_inv_mul_indicator_shell_of_cuspidal
    (p : HeightOneSpectrum (𝓞 ℚ))

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

    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)

    (E₀ : ℂ) (e₀ : ℤ)
    (hfe : letI := localBorel ℚ p
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₀ σ₁ : ℝ),
        (∀ s : ℂ, σ₀ < s.re →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, σ₀ < s.re →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y * wJ) * (((χ y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
              ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y * wJ) * (((χ y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ,
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            (E₀ * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e₀ : ℂ) * s)) *
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))))

    (hcusp : ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ N₀ : ℤ, ∀ y : (p.adicCompletion ℚ)ˣ, Valued.v (y : (p.adicCompletion ℚ)) ≤ WithZero.exp N₀ → v (diagOne y) = 0)
    :
    ∀ (m : ℤ),
    ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      (∀ y : (p.adicCompletion ℚ)ˣ,
        w₂ (diagOne y) = (((χ y : ℂˣ) : ℂ))⁻¹ * (if Valued.v (y : (p.adicCompletion ℚ)) = WithZero.exp (-m) then (1 : ℂ) else 0)) →
      ∀ y : (p.adicCompletion ℚ)ˣ,
        w₂ (diagOne y * wJ) =
          E₀ * (Ideal.absNorm p.asIdeal : ℂ) ^ (((e₀ : ℤ) : ℂ) / 2) * ((χ y : ℂˣ) : ℂ) * ((θ₀ y : ℂˣ) : ℂ) *
            (if Valued.v (y : (p.adicCompletion ℚ)) = WithZero.exp (-(e₀ - m)) then (1 : ℂ) else 0) := by sorry
