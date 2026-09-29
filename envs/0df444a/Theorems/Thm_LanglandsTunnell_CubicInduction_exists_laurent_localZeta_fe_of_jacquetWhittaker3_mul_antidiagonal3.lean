-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3
-- name    : LanglandsTunnell.CubicInduction.exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/acf22cef-cca7-5f7b-b6d7-0c8ebf4d5ec9
-- title:
--   Local Laurent form and functional equation of the GL₃ Whittaker zeta integrals
-- statement:
--   Let $v$ be a nonzero prime of the ring of integers of $\mathbb{Q}$, with completion $\mathbb{Q}_v$ and residue norm $q_v=\mathrm{absNorm}(v)$. Fix three locally constant characters $\nu_0,\nu_1,\nu_2\colon \mathbb{Q}_v^{\times}\to\mathbb{C}^{\times}$, a locally constant compactly supported $\Phi\colon \mathbb{Q}_v^{3}\to\mathbb{C}$, and a locally constant character $\chi$, and assume $|(\nu_i\chi)(\varpi_v)|=1$ for each $i$, $\varpi_v$ being `uniformizerUnit`. Write $W(h)=$ `jacquetWhittaker3 v ν Φ` evaluated at $h\cdot w$, where $w=$ `antidiagonal3` is the antidiagonal permutation matrix of $GL_3(\mathbb{Q}_v)$, and let $\mu$ be the measure on $\mathbb{Q}_v^{\times}$ obtained by pulling back along $u\mapsto u$ the measure $|x|^{-1}\,dx$ on $\mathbb{Q}_v\setminus\{0\}$, $dx$ the self-dual Haar measure `selfDualHaarAt` attached to $\psi_v$. Then there are $P\colon\mathbb{C}\to\mathbb{C}$ and $\sigma_0,\sigma_1\in\mathbb{R}$ such that: $P(s)=Q(q_v^{-s})\,q_v^{ms}$ for some polynomial $Q$ and $m\in\mathbb{N}$; the torus integrand $a\mapsto W(\iota(\mathrm{diag}(a))) \chi(a)|a|^{s-1}$ is $\mu$-integrable for $\mathrm{Re}\,s>\sigma_0$, and there `localZeta30` equals $\big(\prod_i L_v(\nu_i\chi,s)\big)P(s)$, the factor being $(1-(\nu_i\chi)(\varpi_v)q_v^{-s})^{-1}$ when $\nu_i\chi$ has conductor exponent $0$ and $1$ otherwise; the dual integrand, built from $h\mapsto W(w_{\mathrm{long}}\cdot{}^{t}h^{-1})$, the character $\chi^{-1}$, the point `weylPrime3 * transposeInv3 1`, and integration over $\mu\times dx$ against the lower unipotent, is integrable for $\mathrm{Re}\,s>\sigma_1$; and there are $a_i\in\mathbb{N}$ with $\nu_i\chi$ trivial on the $a_i$-th higher unit group and nontrivial on each lower one such that, for $\mathrm{Re}(1-s)>\sigma_1$, `localZetaDual31` at $1-s$ and the identity equals $\big(\prod_i L_v((\nu_i\chi)^{-1},1-s)\big)\big(\prod_i \varepsilon_v(\nu_i\chi,1/2)\big)q_v^{(\sum_i a_i)(1/2-s)}P(s)$.
--
--   This is the local functional equation, in Laurent-polynomial form, for the zeta integrals of the Jacquet–Whittaker function of a cell section on $GL_3$ at a finite place of $\mathbb{Q}$: one half-plane statement for the torus integral and one for the dual integral with the unipotent variable, linked by the same Laurent polynomial $P$ and by the product of the local $L$-factors and root numbers of the twists $\nu_i\chi$. It supplies the local input at the ramified places to `exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad`, in the converse-theorem step towards the Langlands–Tunnell theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.RankinSelberg
  LanglandsTunnell.TateLocal MeasureTheory

theorem LanglandsTunnell.CubicInduction.exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1) :
    letI := localBorel ℚ v
    ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
      (∃ (Q : Polynomial ℂ) (m : ℕ), ∀ s : ℂ,
        P s = Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
      IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
        (fun h => jacquetWhittaker3 v ν Φ (h * antidiagonal3 v)) χ 1 σ₀ ∧
      (∀ s : ℂ, σ₀ < s.re →
        localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
            (fun h => jacquetWhittaker3 v ν Φ (h * antidiagonal3 v)) χ s 1 =
          (∏ i, LanglandsTunnell.TateLocal.localLFactorAt ℚ v (ν i * χ) s) * P s) ∧
      IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
        (dualWhittakerFn3 (fun h => jacquetWhittaker3 v ν Φ (h * antidiagonal3 v)))
        χ⁻¹ (weylPrime3 * transposeInv3 1) σ₁ ∧
      ∃ a : Fin 3 → ℕ, (∀ i, LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (ν i * χ) (a i)) ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
              (fun h => jacquetWhittaker3 v ν Φ (h * antidiagonal3 v)) χ (1 - s) 1 =
            (∏ i, LanglandsTunnell.TateLocal.localLFactorAt ℚ v (ν i * χ)⁻¹ (1 - s)) *
              ((∏ i, LanglandsTunnell.TateLocal.stdRootNumberAt ℚ v (ν i * χ)) *
                (Ideal.absNorm v.asIdeal : ℂ) ^ ((∑ i, (a i : ℂ)) * (1 / 2 - s))) * P s := by sorry
