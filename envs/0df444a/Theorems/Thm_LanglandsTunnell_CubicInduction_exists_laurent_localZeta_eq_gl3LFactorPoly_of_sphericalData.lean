-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData
-- name    : LanglandsTunnell.CubicInduction.exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/9ce40b84-f529-59fb-b5a3-546e98f65ced
-- title:
--   Local functional equation for spherical GL₃ Whittaker zeta integrals
-- statement:
--   Let $v$ be a finite place of $\mathbb{Q}$, with residue cardinality $q_v=\mathrm{absNorm}(v)$ and uniformiser $\varpi_v$, let $W:\mathrm{GL}_3(\mathbb{Q}_v)\to\mathbb{C}$ and let $e_1,e_2,e_3\in\mathbb{C}$. Assume, as the four conjuncts of `hW`: $W$ is right invariant under the subgroup `localMaximalCompact3` of those $k$ with all entries of $k$ and of $k^{-1}$ of valuation $\le 1$; for every finite family of representatives forming a Hecke coset system for the double coset of $\mathrm{diag}(\varpi_v,1,1)$ (respectively $\mathrm{diag}(\varpi_v,\varpi_v,1)$) one has $\sum_i W(g\,r_i)=q_v e_1 W(g)$ (respectively $q_v e_2 W(g)$) for all $g$; and $W(\mathrm{diag}(\varpi_v,\varpi_v,\varpi_v)g)=e_3W(g)$. Assume further $W(u(x,y,z)g)=\psi_v(x+y)W(g)$ for the standard local additive character $\psi_v$ and all upper unipotent $u(x,y,z)$. Let $\chi:\mathbb{Q}_v^\times\to\mathbb{C}^\times$ have conductor exponent $a$ (trivial on the $a$-th higher unit set, nontrivial on each smaller one), with $\|\chi(\varpi_v)\|=1$ and $t=\chi(\varpi_v)$, and let $g\in\mathrm{GL}_3(\mathbb{Q}_v)$. Then, with $\mathbb{Q}_v$ carrying its Borel structure and $\mu$ the multiplicative measure on $\mathbb{Q}_v^\times$ obtained from the self-dual additive measure $\nu$, two assertions hold. If $a=0$, there are $P:\mathbb{C}\to\mathbb{C}$ of the form $P(s)=Q(q_v^{-s})\,q_v^{ms}$ with $Q\in\mathbb{C}[X]$ and $m\in\mathbb{N}$, and $\sigma_0,\sigma_1\in\mathbb{R}$, such that the integrand of `localZeta30` (that is, $a\mapsto W(\iota(\mathrm{diag}(a,1))g)\chi(a)|a|^{s-1}$) is $\mu$-integrable for $\mathrm{Re}\,s>\sigma_0$ and there $$\mathrm{localZeta30}=\big(1-te_1X+t^2e_2X^2-t^3e_3X^3\big)^{-1}\big|_{X=q_v^{-s}}P(s),$$ while the integrand of `localZeta31` for the dual function $h\mapsto W(w_{\mathrm{long}}\,{}^t h^{-1})$, the character $\chi^{-1}$ and the point `weylPrime3`$\cdot\,{}^tg^{-1}$ is $\mu\times\nu$-integrable for $\mathrm{Re}\,s>\sigma_1$, and for $\sigma_1<\mathrm{Re}(1-s)$ the dual integral `localZetaDual31` at $1-s$, divided by $\nu(\mathcal{O}_v)$, equals $\big(1-t^{-1}(e_2/e_3)X+t^{-2}(e_1/e_3)X^2-t^{-3}e_3^{-1}X^3\big)^{-1}\big|_{X=q_v^{-(1-s)}}P(s)$. If $a\ge 1$, the same data exist with the first identity reading $\mathrm{localZeta30}=P(s)$ and the second $e_3^{a}\,\varepsilon(\chi)^3\,q_v^{3a(1/2-s)}P(s)$, where $\varepsilon(\chi)$ is the standard local root number `stdRootNumberAt`.
--
--   This is the local computation at a finite place of the functional equation relating the $\mathrm{GL}_3\times\mathrm{GL}_1$ zeta integral of a spherical Whittaker vector with prescribed Hecke eigenvalues to its dual integral, in the form required by the Jacquet–Piatetski-Shapiro–Shalika converse theorem: the ratio is the inverse cubic Euler factor $1-te_1X+t^2e_2X^2-t^3e_3X^3$ in the unramified case and a monomial root-number factor in the ramified case. It is used in the assembly of the global functional equation for the candidate automorphic representation in the cubic induction step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_JPSS_CubicLiftFactor
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.RankinSelberg
  LanglandsTunnell.TateLocal MeasureTheory

theorem LanglandsTunnell.CubicInduction.exists_laurent_localZeta_eq_gl3LFactorPoly_of_sphericalData
    (v : HeightOneSpectrum (𝓞 ℚ)) (W : LocalGL3 v → ℂ) (e₁ e₂ e₃ : ℂ)
    (hW : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) W (cNormQ v * e₁) ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) W (cNormQ v * e₂) ∧
      ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g)
    (hψ : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ v) W)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (a : ℕ) (hχa : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v χ a)
    (hu : ‖((χ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (t : ℂ) (ht : t = ((χ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)) (g : LocalGL3 v) :
    letI := localBorel ℚ v
    (a = 0 →
      ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
        (∃ (Q : Polynomial ℂ) (m : ℕ), ∀ s : ℂ,
          P s = Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
        IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
          W χ g σ₀ ∧
        (∀ s : ℂ, σ₀ < s.re →
          localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ s g =
            ((gl3LFactorPoly (t * e₁) (t ^ 2 * e₂) (t ^ 3 * e₃)).eval
                ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹ * P s) ∧
        IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
          (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) χ⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          ((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ)⁻¹ *
              localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
                (selfDualHaarAt ℚ v) W χ (1 - s) g =
            ((gl3LFactorPoly (t⁻¹ * (e₂ / e₃)) (t⁻¹ ^ 2 * (e₁ / e₃)) (t⁻¹ ^ 3 * e₃⁻¹)).eval
                ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))))⁻¹ * P s) ∧
    (1 ≤ a →
      ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
        (∃ (Q : Polynomial ℂ) (m : ℕ), ∀ s : ℂ,
          P s = Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
        IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
          W χ g σ₀ ∧
        (∀ s : ℂ, σ₀ < s.re →
          localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W χ s g =
            P s) ∧
        IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
          (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) χ⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          ((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ)⁻¹ *
              localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
                (selfDualHaarAt ℚ v) W χ (1 - s) g =
            (e₃ ^ a * LanglandsTunnell.TateLocal.stdRootNumberAt ℚ v χ ^ 3 *
                (Ideal.absNorm v.asIdeal : ℂ) ^ (((3 * a : ℕ) : ℂ) * (1 / 2 - s))) * P s) := by sorry
