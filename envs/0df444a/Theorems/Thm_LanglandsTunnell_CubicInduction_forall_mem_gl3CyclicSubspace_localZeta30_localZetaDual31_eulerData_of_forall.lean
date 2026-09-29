-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_localZeta30_localZetaDual31_eulerData_of_forall
-- name    : LanglandsTunnell.CubicInduction.forall_mem_gl3CyclicSubspace_localZeta30_localZetaDual31_eulerData_of_forall
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/bc9483a8-3c7f-5c92-b695-115a5df373ce
-- title:
--   Local GL₃ zeta data passes to the cyclic span
-- statement:
--   Fix a finite place $v$ of $\mathbf{Q}$, i.e. $v \in$ `HeightOneSpectrum (𝓞 ℚ)`, write $q =$ `Ideal.absNorm v.asIdeal` for the residue cardinality, and let $W : GL_3(\mathbf{Q}_v) \to \mathbf{C}$ be an arbitrary function on `LocalGL3 v`, $E, Ed$ complex polynomials, $\varepsilon \in \mathbf{C}$ and $\ell \in \mathbf{N}$. Throughout, $\mathbf{Q}_v$ carries the Borel structure `localBorel ℚ v`, the additive measure is `selfDualHaarAt ℚ v`, and the measure on $\mathbf{Q}_v^\times$ is the pullback along `Units.val` of `mulMeasure (selfDualHaarAt ℚ v)`; the character is the trivial one. The hypothesis is that for every $g \in GL_3(\mathbf{Q}_v)$ there are $P : \mathbf{C} \to \mathbf{C}$ and reals $\sigma_0, \sigma_1$ with: (i) polynomials $Q, R$ with $R \neq 0$ and $m \in \mathbf{N}$ such that $P(s)R(q^{-s}) = Q(q^{-s})q^{ms}$ for all $s$; (ii) `IsLocalZeta30ConvergentAbove` for $W$ at $g$ above $\sigma_0$, i.e. for $\operatorname{Re} s > \sigma_0$ the function $a \mapsto W(\iota(\mathrm{diag}(a,1))g)\,|a|^{s-1}$ is integrable on $\mathbf{Q}_v^\times$; (iii) $\mathrm{localZeta30}(s) = \int W(\iota(\mathrm{diag}(a,1))g)|a|^{s-1}\,d^\times a$ equals $E(q^{-s})^{-1}P(s)$ there; (iv) `IsLocalZeta31ConvergentAbove` for the dual function `dualWhittakerFn3 W`, $x \mapsto W(w_3\,{}^t x^{-1})$, at $w'\,{}^t g^{-1}$ above $\sigma_1$, integrability of $(a,x) \mapsto (\mathrm{dualWhittakerFn3}\,W)(\iota(\mathrm{diag}(a,1))\,n_{21}(x)\,w'\,{}^tg^{-1})|a|^{s-1}$ on the product measure; and (v) for $\operatorname{Re}(1-s) > \sigma_1$, $\mathrm{localZetaDual31}(1-s)$, namely the $(3,1)$ integral of `dualWhittakerFn3 W` with inverse character at $w'\,{}^tg^{-1}$, equals $Ed(q^{-(1-s)})^{-1}\bigl(\varepsilon q^{\ell(1/2-s)}P(s)\bigr)$. The conclusion asserts the same five clauses, with the same $E$, $Ed$, $\varepsilon$, $\ell$ but $P, \sigma_0, \sigma_1$ allowed to depend on the data, for every $W'$ in `gl3CyclicSubspace W`, the $\mathbf{C}$-span of the functions `gl3AmbientRightTranslate h W` for $h \in GL_3(\mathbf{Q}_v)$, and every $g$.
--
--   This is the transport step in the local theory of $GL_3 \times GL_1$ Rankin–Selberg integrals: a functional-equation package with prescribed Euler factors $E$, $Ed$, root number $\varepsilon$ and conductor exponent $\ell$, known at one Whittaker-type function, holds at every element of the span of its right translates. It feeds the member-wise local functional-equation and Euler-datum statements used in the cubic induction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_localZeta30_localZetaDual31_eulerData_of_forall.lean

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker

theorem LanglandsTunnell.CubicInduction.forall_mem_gl3CyclicSubspace_localZeta30_localZetaDual31_eulerData_of_forall
    (v : HeightOneSpectrum (𝓞 ℚ)) (W : LocalGL3 v → ℂ) (E Ed : Polynomial ℂ) (ε : ℂ) (ℓ : ℕ)
    (h31 : ∀ g : LocalGL3 v,
      (letI := localBorel ℚ v
       ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
        (∃ (Q R : Polynomial ℂ) (m : ℕ), R ≠ 0 ∧ ∀ s : ℂ,
          P s * R.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
            Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
        IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 g σ₀ ∧
        (∀ s : ℂ, σ₀ < s.re →
          localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 s g =
            (E.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹ * P s) ∧
        IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
          (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) 1 (weylPrime3 * transposeInv3 g) σ₁ ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
              W 1 (1 - s) g =
            (Ed.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))))⁻¹ *
              ((ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s))) * P s))) :
    ∀ W' ∈ gl3CyclicSubspace W, ∀ g : LocalGL3 v,
      (letI := localBorel ℚ v
       ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
        (∃ (Q R : Polynomial ℂ) (m : ℕ), R ≠ 0 ∧ ∀ s : ℂ,
          P s * R.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
            Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
        IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W' 1 g σ₀ ∧
        (∀ s : ℂ, σ₀ < s.re →
          localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W' 1 s g =
            (E.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹ * P s) ∧
        IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
          (selfDualHaarAt ℚ v) (dualWhittakerFn3 W') 1 (weylPrime3 * transposeInv3 g) σ₁ ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
              W' 1 (1 - s) g =
            (Ed.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))))⁻¹ *
              ((ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s))) * P s)) := by sorry
