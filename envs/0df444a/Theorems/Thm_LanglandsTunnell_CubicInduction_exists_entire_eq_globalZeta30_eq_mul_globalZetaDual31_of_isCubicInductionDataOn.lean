-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_entire_eq_globalZeta30_eq_mul_globalZetaDual31_of_isCubicInductionDataOn
-- name    : LanglandsTunnell.CubicInduction.exists_entire_eq_globalZeta30_eq_mul_globalZetaDual31_of_isCubicInductionDataOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/ff7a7ea3-38d7-5435-b596-cb86564abc9a
-- title:
--   Entire continuation and functional equation of GL₃ zeta integrals
-- statement:
--   Let $K$ be a number field equipped with an integral $\mathcal{O}_{\mathbb{Q}}$-algebra structure on $\mathcal{O}_K$ and with $[K:\mathbb{Q}]=3$; let $\psi$ be an additive character of $\mathbb{A}_{\mathbb{Q}}$ that is trivial on principal adeles, continuous and nontrivial; let $\mu:\mathbb{A}_K^\times\to\mathbb{C}^\times$ be continuous, unitary and trivial on $K^\times$. Assume that at every finite place $v$ of $\mathbb{Q}$ which is neither ramified in $K$ nor carries a prime of $K$ above it at which $\mu$ is ramified, the local component `psiLoc` $\psi$ $v$ has `addCharLevel` equal to $0$; and assume $\mu$ is not a norm twist, i.e. there is no continuous unitary idele class character $\eta$ of $\mathbb{Q}$ with $\mu(\varpi_{\mathfrak{P}})=\eta(\varpi_{v})^{f(\mathfrak{P}/v)}$ for all primes $\mathfrak{P}$ of $K$ unramified for $\mu$ whose trace $v$ is unramified for $\eta$. Fix data $D$, $U$, `gen` defining the carrier pins `productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)` (adelic $\mathrm{GL}_2$ Borel structure and Haar measure, full central subgroup, adelic additive measure conditioned on the adelic box), a set $S$ of finite places of $\mathbb{Q}$, and $X$ a `CubicInductionData`, consisting of a form $\phi$ on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$, a global Whittaker function $W$, local Whittaker functions $W_v$, an archimedean $W_\infty$, a central character $\omega$ and a dual Whittaker function $\widetilde W$. Assume `IsCubicInductionDataOn K` holds for these pins, $\psi$, $\mu$, $S$ and $X$: $\phi$ is invariant under $\mathrm{GL}_3(\mathbb{Q})$ on the left and transforms by the idele class character $\omega$ under the centre, is cuspidal along the radicals of $P_{21}$ and $P_{12}$, has moderate growth, and satisfies the iota-moment condition; $W$ is the $\psi$-Whittaker integral `whittaker3` of $\phi$ over the conditioned box measure, satisfies the $\psi$-Whittaker transformation law, expands as a convergent sum $\sum_i W(\text{mirabolicTranslate } i\cdot g)=\phi(g)$ over the mirabolic index set, factors at each $g$ as $W_\infty$ times a finite product of the $W_v$ over any finite $T\supseteq S$ outside which $g$ is integral, and satisfies the half-plane convergence condition; each $W_v$ satisfies the local $\psi_v$-Whittaker law and local multiplicity one, is spherical with the induced Hecke eigenvalues built from `inducedCoeff K μ` for $v\notin S$ and invariant under the congruence subgroup `congruenceK1` of level `inducedLevelAt K μ v` when moreover $v$ is unramified in $K$; $W_\infty$ is $K$-finite; and $\widetilde W$ is the $\psi^{-1}$-Whittaker integral of $g\mapsto\phi({}^tg^{-1})$, satisfying the corresponding $\psi^{-1}$-Whittaker law, mirabolic expansion, moment and half-plane conditions. Assume further that $\phi$, $W$ and $\widetilde W$ are continuous, that $W$ and $\widetilde W$ are gauge-majorised in the sense of `IsGaugeMajorised3` (supported in a root level and bounded there by $C/(\text{root size}^t(1+\text{archimedean root sum})^N)$ for every $N$), and that $c\in\mathbb{C}$ is the inverse of the adelic Haar volume of the adelic box. Then for every $g\in\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ and every continuous unitary idele class character $\chi$ of $\mathbb{Q}$ there exist an entire function $E:\mathbb{C}\to\mathbb{C}$, bounded on every vertical strip, and reals $\sigma_1,\sigma_2$ such that $E(s)=\int_{\mathbb{A}^\times}W(\mathrm{diag}(a,1,1)g)\chi(a)\|a\|^{s-1}\,d^\times a$ for $\operatorname{Re}s>\sigma_1$, and $E(s)=c\cdot\int_{\mathbb{A}^\times}\bigl(\int_{\mathbb{A}}W(w_3\,{}^t(\mathrm{diag}(a,1,1)u_{21}(x)w'\,{}^tg^{-1})^{-1})\,dx\bigr)\chi(a)^{-1}\|a\|^{-s}\,d^\times a$ for $\operatorname{Re}s<\sigma_2$, the integrals being `globalZeta30 X.whittaker χ s g` and $c\cdot$`globalZetaDual31 X.whittaker χ (1-s) g` taken against idelic and adelic Haar measure.
--
--   This is the analytic continuation and functional equation of the $\mathrm{GL}_3\times\mathrm{GL}_1$ global zeta integral attached to a Whittaker function, in the shape required by the converse theorem: the rank-zero integral $Z(s,W,\chi;g)$ and the dual rank-one integral at $1-s$ are two expansions of one entire function bounded on vertical strips. It feeds the extraction of local gamma factors and root numbers at the bad and ramified places for the automorphic representation induced from an idele class character of a cubic field, the input to the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_entire_eq_globalZeta30_eq_mul_globalZetaDual31_of_isCubicInductionDataOn.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.CubicInduction

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in

theorem LanglandsTunnell.CubicInduction.exists_entire_eq_globalZeta30_eq_mul_globalZetaDual31_of_isCubicInductionDataOn
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hμ : IsAdmissibleTwist K μ)
    (_hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (_hns : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (S : Set (HeightOneSpectrum (𝓞 ℚ)))
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ S X)
    (hcont : Continuous X.form) (hW : IsGaugeMajorised3 ℚ X.whittaker) (hW' : IsGaugeMajorised3 ℚ X.dualWhittaker)
    (hcontW : Continuous X.whittaker) (hcontW' : Continuous X.dualWhittaker)
    (c : ℂ) (hc : c * ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ)).toReal : ℂ) = 1) :
    ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ∀ χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ χ →
        ∃ E : ℂ → ℂ, Differentiable ℂ E ∧ LanglandsTunnell.LDatum.BoundedOnStrips E ∧ ∃ σ₁ σ₂ : ℝ,
          (∀ s : ℂ, σ₁ < s.re → E s = globalZeta30 X.whittaker χ s g) ∧
          (∀ s : ℂ, s.re < σ₂ → E s = c * globalZetaDual31 X.whittaker χ (1 - s) g) := by sorry
