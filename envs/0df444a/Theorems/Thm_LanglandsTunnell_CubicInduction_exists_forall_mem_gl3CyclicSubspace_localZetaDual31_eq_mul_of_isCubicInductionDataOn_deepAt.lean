-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_mem_gl3CyclicSubspace_localZetaDual31_eq_mul_of_isCubicInductionDataOn_deepAt
-- name    : LanglandsTunnell.CubicInduction.exists_forall_mem_gl3CyclicSubspace_localZetaDual31_eq_mul_of_isCubicInductionDataOn_deepAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/dbe0b9eb-cf91-5e2a-a577-9d02134cb207
-- title:
--   Local GL₃timesGL₁ constants of a cubic induction at one bad place
-- statement:
--   **Setting.** Let $K$ be a number field of degree $3$ over $\mathbb{Q}$ (the hypothesis `_hdeg` records $\operatorname{finrank}_{\mathbb{Q}} K = 3$), with $\mathcal{O}_K$ an integral $\mathcal{O}_{\mathbb{Q}}$-algebra, and let $\mu\colon (\mathbb{A}_K)^\times \to \mathbb{C}^\times$ be a character which is *admissible* in the sense of `IsAdmissibleTwist`: trivial on the principal idèles $K^\times$, continuous, and of absolute value $1$ everywhere. The hypothesis `hoff` asserts that $\mu$ is not of norm type in the following sense: there is no admissible character $\eta$ of $(\mathbb{A}_{\mathbb{Q}})^\times$ such that for every prime $\mathfrak{P}$ of $\mathcal{O}_K$ at which $\mu$ is unramified and whose underlying prime $p=\mathfrak{P}\cap\mathcal{O}_{\mathbb{Q}}$ is unramified for $\eta$, one has $\mu(\varpi_{\mathfrak{P}}) = \eta(\varpi_{p})^{f(\mathfrak{P}/p)}$, the uniformiser idèles being those produced by `uniformizerIdele` and $f$ the residue degree `inertiaDeg'`. Let $p$ be a finite place of $\mathbb{Q}$ which is *bad* for $(K,\mu)$, i.e. `IsBadPlace K μ p`: either some prime of $\mathcal{O}_K$ above $p$ has ramification index $\neq 1$, or $\mu$ is ramified at some prime above $p$.
--
--   **Archimedean parameters and additive character.** Families $u^{\mathbb{R}}_w, a^{\mathbb{R}}_w$ (indexed by the real places $w$ of $K$, with $a^{\mathbb{R}}_w \in \mathbb{Z}/2$) and $u^{\mathbb{C}}_w, k^{\mathbb{C}}_w$ (indexed by the complex places, with $k^{\mathbb{C}}_w \in \mathbb{Z}$) are given, together with hypotheses `hcR`, `hcC` saying that these are the archimedean components of $\mu$ in the sense of `IsArchCompAt`: the local component of $\mu$ at $w$ sends $x$ to $\lVert x\rVert^{m_w u_w}\,(x/\lVert x\rVert)^{a_w}$, with $a_w$ the integer lift of $a^{\mathbb{R}}_w$ at a real place and $k^{\mathbb{C}}_w$ at a complex place. Further, $\psi$ is an additive character of $\mathbb{A}_{\mathbb{Q}}$ which is global (`IsGlobalAddChar`: trivial on $\mathbb{Q}$, continuous, non-trivial), whose local component `psiLoc ψ v` has level $0$ at every finite place $v$ (`hlev`), and whose inverse is the standard character $\psi_{\mathbb{Q}}$ (`hψQ`).
--
--   **The central character $\omega_3$ and the archimedean data.** A character $\omega_3$ of $(\mathbb{A}_{\mathbb{Q}})^\times$ is given, and `hω₃` has three clauses: $\omega_3$ is admissible; at every finite place $p'$ which is not bad for $(K,\mu)$, $\omega_3$ is unramified with Euler coefficient $\omega_3(\varpi_{p'})$ equal to `inducedE3 ℚ (inducedCoeff K μ) p'`, minus the coefficient of $X^3$ in the induced Euler polynomial $\prod_{w\mid p'}$ of the Frobenius data `inducedCoeff K μ`; and, for any families $u^{\mathbb{R}},a^{\mathbb{R}},u^{\mathbb{C}},k^{\mathbb{C}}$ satisfying the same two `IsArchCompAt` conditions, the archimedean component of $\omega_3$ at the real place of $\mathbb{Q}$ has exponent $\sum_w u^{\mathbb{R}}_w + \sum_w 2u^{\mathbb{C}}_w$ and integer parameter $\sum_w (a^{\mathbb{R}}_w)^{\mathrm{val}} + \sum_w (k^{\mathbb{C}}_w+1)$, the sums being finite sums over the real, resp. complex, places of $K$.
--
--   A monoid homomorphism $E\colon (\mathbb{A}_{\mathbb{Q},\infty})^\times \to (\mathbb{A}_{\mathbb{Q}})^\times$ is given with $E(u)$ having infinite part $u$ and trivial finite part (`hE`). A non-zero rational number $a$ is given, together with an infinite idèle $a_\infty$ whose underlying element is the image of $a$, an additive character $\psi_\infty$ of $\mathbb{A}_{\mathbb{Q},\infty}$ with $\psi_\infty(x) = \psi_{\mathrm{arch}}(a x)$, and the compatibility `hψinf` that the restriction of $\psi$ to the infinite component is $\psi_\infty$. Measures: $\nu_{\mathrm{add}}$ on $\mathbb{A}_{\mathbb{Q},\infty}$ is $|a|^{1/2}$ times the transport of Lebesgue measure along the inverse of the identification of $\mathbb{A}_{\mathbb{Q},\infty}$ with the mixed space, and $\nu_{\mathrm{mul}}$ is a Haar measure on $(\mathbb{A}_{\mathbb{Q},\infty})^\times$; the Borel structures on $\mathbb{A}_{\mathbb{Q},\infty}$ and its unit group are the ones in force.
--
--   **The archimedean Whittaker package `hWarch`.** A function $W_{\mathrm{arch}}$ on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q},\infty})$ is given satisfying, in conjunction: $W_{\mathrm{arch}} \neq 0$ and $K$-finite (the right translates by the orthogonal set `orth3` span a finite-dimensional space); continuous, with a moderate-growth bound $\lVert W_{\mathrm{arch}}(g_\infty)\rVert \le C/\big((\prod_w \mathrm{archRoot}_1\,\mathrm{archRoot}_2)^t (1+\mathrm{archRootSum})^N\big)$ for some $t$ and, for each $N$, some $C$; the Whittaker transformation law $W_{\mathrm{arch}}(u(x,y,z)g) = \psi_\infty(x+y)W_{\mathrm{arch}}(g)$ for the upper unipotent `upperUnipotent3`; the central law $W_{\mathrm{arch}}(z\cdot g) = \omega_3(E z)W_{\mathrm{arch}}(g)$ for scalar matrices; and an archimedean functional-equation clause, namely for every admissible character $\sigma$ of $(\mathbb{A}_{\mathbb{Q}})^\times$, every $t \in \mathbb{C}$ and $e \in \mathbb{Z}$ which are the archimedean parameters of $\sigma$ at the real place, and every $g_\infty \in \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q},\infty})$, the existence of an entire function $P$ with: a half-plane $\sigma_0$ above which the $\mathrm{GL}_3\times\mathrm{GL}_1$ archimedean zeta integral `archZeta30` of $h \mapsto W_{\mathrm{arch}}(h g_\infty)$ against $\sigma\circ E$ converges and equals $P(s)$ times the archimedean factor of the Hecke $L$-datum `heckeDatum K μ` with parameters shifted to $u^{\mathbb{R}}+t$, $a^{\mathbb{R}}+e$, $u^{\mathbb{C}}+t$, $k^{\mathbb{C}}$; bounds $\lVert P(s)\rVert \le C e^{A|\operatorname{Im} s|}$ in every vertical strip; rapid decay of $|\operatorname{Im} s|^N \lVert P(s)\,\Gamma\text{-factor}\rVert$ in every strip; and a half-plane $\sigma_1$ above which the dual integral `archZeta31` of `dualWhittakerFn3` at `weylPrime3 * transposeInv3 1` converges, with, for $\operatorname{Re}(1-s) > \sigma_1$,
--   $$\mathrm{archZetaDual31}(1-s) = \Big(\textstyle\prod_{w\ \mathrm{real}} \varepsilon(a^{\mathbb{R}}_w+e)\cdot\prod_{w\ \mathrm{complex}} i^{|k^{\mathbb{C}}_w|}\cdot\prod_{w} \lambda_{\mathrm{arch}}(w)\Big)\,\big(\omega_3(E a_\infty)\,\sigma(E a_\infty)^3\big)\,|a|^{3(s-1/2)}\,P(s)\,\Gamma^{\vee}(1-s),$$
--   where $\varepsilon$ is `signEpsilon`, the products run over the real and complex places of $K$, and $\Gamma^{\vee}$ is the dual archimedean factor of the same shifted $L$-datum. A final clause provides an admissible $\sigma$ and a point $s$ at which `archZeta30 ν_mul Warch (σ.comp E) s 1` is non-zero.
--
--   **The cubic induction data.** Data $D$, $U$, `gen` for the $\mathrm{GL}_2$ carrier pins over $\mathbb{Q}$ are given, and $X$ is a `CubicInductionData`, i.e. a tuple consisting of a form `X.form` on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$, its Whittaker function `X.whittaker`, local Whittaker functions `X.whittakerLoc v` on $\mathrm{GL}_3(\mathbb{Q}_v)$, an archimedean Whittaker function `X.whittakerArch`, a central character `X.centralChar`, and a dual Whittaker function `X.dualWhittaker`. The hypothesis `hX` asserts `IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ μ S X` with $S$ the set of bad places of $(K,\mu)$; its clauses (summarised here) require: left invariance of `X.form` under $\mathrm{GL}_3(\mathbb{Q})$ and the central law with idèle-class character `X.centralChar`; cuspidality along the two maximal parabolic radicals; that `X.whittaker` is the $\psi$-Whittaker integral of `X.form` over the pins' measure and satisfies the $\psi$-Whittaker law, with the mirabolic Fourier expansion summing to `X.form`; the $\psi_v$-Whittaker law for each `X.whittakerLoc v`; factorisation of `X.whittaker` into `X.whittakerArch` times a finite product of local factors for any finite set containing $S$ and away from which the components are integral; at places outside $S$, sphericity of `X.whittakerLoc v` with Hecke eigenvalues given by `inducedE1`, `inducedE2`, `inducedE3` of `inducedCoeff K μ`, and invariance under the congruence subgroup of level `inducedLevelAt K μ v` at unramified places; Whittaker multiplicity one locally; moderate growth of `X.form`, $K$-finiteness of `X.whittakerArch`, the iota-moment and Whittaker half-plane integrability conditions; and the corresponding statements for `X.dualWhittaker` relative to $\psi^{-1}$ and the dual form.
--
--   In addition: `hX0` asserts `X.form ≠ 0` and that at every non-bad place $v$ at which `psiLoc ψ v` has level $0$ one has `X.whittakerLoc v 1 = 1` together with `HasSphericalTorusValuesAt (inducedCoeff K μ) v (X.whittakerLoc v)`; `hX1` asserts `X.whittakerLoc w 1 = 1` at every bad place $w$; `hXc`, `hXw`, `hXdw` are continuity of `X.form`, `X.whittaker`, `X.dualWhittaker`; `hXg`, `hXdg` are the gauge-majorisation conditions `IsGaugeMajorised3` for `X.whittaker` and `X.dualWhittaker`; `hArchEq` identifies `X.whittakerArch` with $W_{\mathrm{arch}}$. The hypothesis `hBad` asserts, for every finite set $T$ of finite places, that at every bad $v \in T$ the function `X.whittakerLoc v` is right invariant under some open subgroup of $\mathrm{GL}_3(\mathbb{Q}_v)$, and that every non-zero element $W$ of the cyclic subspace generated by `X.whittakerLoc v` generates `X.whittakerLoc v` in turn. The hypothesis `hadm` asserts, at every bad $w$ and every open subgroup $U_w$, the existence of a finite set of functions whose $\mathbb{C}$-span contains all $U_w$-right-invariant vectors of the cyclic subspace of `X.whittakerLoc w`. The hypothesis `hcent` asserts, at every bad $w$, that the local component of `X.centralChar` at $w$ is unitary and that `X.whittakerLoc w` transforms under the central torus of $\mathrm{GL}_3(\mathbb{Q}_w)$ by that character.
--
--   **Conclusion.** There exists $\lambda \in \mathbb{C}$, $\lambda \neq 0$, with the following property. Let $W$ be any element of `gl3CyclicSubspace (X.whittakerLoc p)`, the $\mathbb{C}$-span of the right translates of `X.whittakerLoc p`. Let $b \in \mathbb{N}$ be such that for every prime $w$ of $\mathcal{O}_K$ above $p$,
--   $$2\,\big(e(w\mid p)\,b\big) + 1 \le a\big(\mu_w\big),$$
--   where $e$ is `ramificationIdx'` and $a(\mu_w)$ is `conductorExponentAt K w (localChar μ w)`. Let $\eta$ be a character of $(\mathbb{Q}_p)^\times$ having conductor exponent $c_\eta$ in the sense of `HasConductorExponentAt` with $c_\eta \le b$, let $\eta_{\mathbb{A}}$ be an admissible character of $(\mathbb{A}_{\mathbb{Q}})^\times$ whose local component at $p$ is $\eta$ and whose base change $\eta_{\mathbb{A}} \circ N$ along the idelic norm of `genuineBaseChange ℚ K` is admissible over $K$, and let $g \in \mathrm{GL}_3(\mathbb{Q}_p)$. Then there exist polynomials $Q_1, Q_2 \in \mathbb{C}[X]$, an integer $n$ and real numbers $\sigma_0, \sigma_1$ such that $Q_2 \neq 0$ and, writing $q = \mathrm{N}p$ for the absolute norm of $p$, $\mathrm{d}^\times x$ for the multiplicative measure obtained from the self-dual additive Haar measure `selfDualHaarAt ℚ p` by `mulMeasure` and pullback along $\mathbb{Q}_p^\times \hookrightarrow \mathbb{Q}_p$, and $\mathrm{d}x$ for `selfDualHaarAt ℚ p` itself:
--
--   (i) the integrals defining the $\mathrm{GL}_3\times\mathrm{GL}_1$ zeta integral `localZeta30` of $W$ against $\eta$ at $g$ converge for $\operatorname{Re} s > \sigma_0$;
--
--   (ii) for all $s$ with $\operatorname{Re} s > \sigma_0$,
--   $$Z(s, W, \eta, g)\;Q_2(q^{-s}) = Q_1(q^{-s})\,q^{n s},$$
--   where $Z$ is `localZeta30`;
--
--   (iii) the double integrals defining `localZeta31` for `dualWhittakerFn3 W` against $\eta^{-1}$ at `weylPrime3 * transposeInv3 g`, with respect to $\mathrm{d}^\times x \otimes \mathrm{d}x$, converge for $\operatorname{Re} s > \sigma_1$;
--
--   (iv) for all $s$ with $\operatorname{Re}(1-s) > \sigma_1$, with the *same* $Q_1$, $Q_2$ and $n$,
--   $$\widetilde Z(1-s, W, \eta, g)\;Q_2(q^{-s}) = Q_1(q^{-s})\,q^{n s}\cdot\Big(\lambda \cdot \prod_{w \mid p}\chi_w(-1) \cdot \prod_{w \mid p}\Big[\varepsilon_w(\chi_w)\,\big(\mathrm{N}w^{\,1/2-s}\big)^{\mathrm{pinnedExp}(\chi, w)}\Big]\Big),$$
--   where $\widetilde Z$ is `localZetaDual31`, $\chi = (\eta_{\mathbb{A}} \circ N)\cdot \mu$ is the product of the base change of $\eta_{\mathbb{A}}$ to $K$ with $\mu$, $\chi_w$ its local component at $w$, $\varepsilon_w$ the standard root number `stdRootNumberAt K w`, $\mathrm{pinnedExp}(\chi,w)$ the sum of the conductor exponent of $\chi_w$ and the level of the standard local additive character at $w$, and both products are finite products over the set of primes $w$ of $\mathcal{O}_K$ above $p$.
--
--   The constant $\lambda$ is independent of $W$, $b$, $\eta$, $c_\eta$, $\eta_{\mathbb{A}}$ and $g$.
--
--   This is the identification, at a single place $p$ bad for $(K,\mu)$, of the local $\mathrm{GL}_3\times\mathrm{GL}_1$ zeta integrals of a cubic induction datum and of their duals: across the whole cyclic span of the local Whittaker function and for all sufficiently deeply ramified local twists, they are the same rational function of $p^{-s}$ up to a monomial, and the local functional equation has the epsilon factor predicted by the induction from $K$, up to one fixed non-zero constant depending only on the place. It feeds the identification wrapper [`LanglandsTunnell.CubicInduction.exists_forall_mem_gl3CyclicSubspace_localZeta31_fe_one_of_cubicInductionForm_twist_deepAt`](thm.html#LanglandsTunnell.CubicInduction.exists_forall_mem_gl3CyclicSubspace_localZeta31_fe_one_of_cubicInductionForm_twist_deepAt), and thence the converse-theorem step of Langlands–Tunnell.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_forall_mem_gl3CyclicSubspace_localZetaDual31_eq_mul_of_isCubicInductionDataOn_deepAt.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory
open LanglandsTunnell.CubicLambda LanglandsTunnell.TateLocal UnramifiedWhittaker
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open scoped Classical in

theorem LanglandsTunnell.CubicInduction.exists_forall_mem_gl3CyclicSubspace_localZetaDual31_eq_mul_of_isCubicInductionDataOn_deepAt
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (hoff : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))

    (p : HeightOneSpectrum (𝓞 ℚ)) (hp : IsBadPlace K μ p)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ)
    (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ)
    (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (hcR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (hcC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ)
    (hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ)

    (ω₃ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω₃ : IsAdmissibleTwist ℚ ω₃ ∧
      (∀ p : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ p →
        IsUnramifiedCharAt ω₃ p ∧ eulerCoeff ℚ ω₃ p = inducedE3 ℚ (inducedCoeff K μ) p) ∧
      ∀ (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
        (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ),
        (∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ)) →
        (∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw)) →
        ∀ v : InfinitePlace ℚ, v.IsReal →
          IsArchCompAt ℚ ω₃ v
            ((∑ᶠ (w) (hw : w.IsReal), uR w hw) + (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw))
            ((∑ᶠ (w) (hw : w.IsReal), ((aR w hw).val : ℤ)) + (∑ᶠ (w) (hw : w.IsComplex), (kC w hw + 1))))
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (a : ℚ) (ha : a ≠ 0) (aInf : (InfiniteAdeleRing ℚ)ˣ)
    (haInf : (aInf : InfiniteAdeleRing ℚ) = algebraMap ℚ (InfiniteAdeleRing ℚ) a)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (hψinf : ψ.compAddMonoidHom
        (AddMonoidHom.inl (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)) = psiInf)
    [mA : MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_add : MeasureTheory.Measure (InfiniteAdeleRing ℚ))
    (hν_add : ν_add = ENNReal.ofReal (|(a : ℝ)| ^ ((1 : ℝ) / 2)) •
      MeasureTheory.Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm MeasureTheory.volume)
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (Warch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ)
    (hWarch :
      Warch ≠ 0 ∧ IsKFinite Warch ∧
      (Continuous Warch ∧ ∃ t : ℕ, ∀ N : ℕ, ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ‖Warch (archComponent3 (𝓞 ℚ) ℚ g)‖ ≤
        C / ((∏ w : InfinitePlace ℚ, archRoot₁ ℚ w g * archRoot₂ ℚ w g) ^ t * (1 + archRootSum ℚ g) ^ N)) ∧
      IsGL3PsiWhittakerFn psiInf Warch ∧
      (∀ (z : (InfiniteAdeleRing ℚ)ˣ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)),
        Warch (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((ω₃ (E z) : ℂˣ) : ℂ) * Warch g) ∧
      (∀ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ →
        ∀ (t : ℂ) (e : ℤ), (∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v t e) →
        ∀ gInf : GL (Fin 3) (InfiniteAdeleRing ℚ), ∃ P : ℂ → ℂ, Differentiable ℂ P ∧
          (∃ σ₀ : ℝ, IsArchZeta30ConvergentAbove ν_mul (fun h => Warch (h * gInf)) (σ.comp E) 1 σ₀ ∧
            ∀ s : ℂ, σ₀ < s.re →
              archZeta30 ν_mul (fun h => Warch (h * gInf)) (σ.comp E) s 1 =
                P s *
                  (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
                    (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactor s) ∧
          (∀ σ₁ σ₂ : ℝ, ∃ C A : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
            ‖P s‖ ≤ C * Real.exp (A * |s.im|)) ∧
          (∀ (σ₁ σ₂ : ℝ) (N : ℕ), ∃ C T₀ : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → T₀ ≤ |s.im| →
            |s.im| ^ N *
              ‖P s *
                (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
                  (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactor s‖ ≤ C) ∧
          (∃ σ₁ : ℝ, IsArchZeta31ConvergentAbove ν_mul ν_add (dualWhittakerFn3 (fun h => Warch (h * gInf)))
              (σ.comp E)⁻¹ (weylPrime3 * transposeInv3 1) σ₁ ∧
            ∀ s : ℂ, σ₁ < (1 - s).re →
              archZetaDual31 ν_mul ν_add (fun h => Warch (h * gInf)) (σ.comp E) (1 - s) 1 =
                (((Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).prod
                    fun w => signEpsilon (aR w.1 w.2 + (e : ZMod 2))) *
                  ((Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).prod
                      fun w => Complex.I ^ (kC w.1 w.2).natAbs) *
                  ∏ w : InfinitePlace K, lambdaArch K w) *
                (((ω₃ (E aInf) : ℂˣ) : ℂ) * ((σ (E aInf) : ℂˣ) : ℂ) ^ 3) *
                (((|a| : ℝ) : ℂ) ^ (3 * (s - 1 / 2))) *
                P s *
                  (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
                    (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactorDual (1 - s))) ∧
      ∃ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ ∧
        ∃ s : ℂ, archZeta30 ν_mul Warch (σ.comp E) s 1 ≠ 0)

    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ μ
      {v : HeightOneSpectrum (𝓞 ℚ) | IsBadPlace K μ v} X)
    (hX0 : X.form ≠ 0 ∧ ∀ v, ¬ IsBadPlace K μ v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
        X.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v (X.whittakerLoc v))
    (hX1 : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w → X.whittakerLoc w 1 = 1)
    (hXc : Continuous X.form) (hXw : Continuous X.whittaker) (hXdw : Continuous X.dualWhittaker)
    (hXg : IsGaugeMajorised3 ℚ X.whittaker) (hXdg : IsGaugeMajorised3 ℚ X.dualWhittaker)
    (hArchEq : X.whittakerArch = Warch)
    (hBad :
        ∀ T : Finset (HeightOneSpectrum (𝓞 ℚ)),
          (∀ v ∈ T, IsBadPlace K μ v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
            ∀ k ∈ Uv, ∀ g : LocalGL3 v, X.whittakerLoc v (g * k) = X.whittakerLoc v g) ∧
          (∀ v ∈ T, IsBadPlace K μ v → ∀ W ∈ gl3CyclicSubspace (X.whittakerLoc v), W ≠ 0 →
            X.whittakerLoc v ∈ gl3CyclicSubspace W))
    (hadm : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w →
      ∀ Uw : Subgroup (LocalGL3 w), IsOpen (Uw : Set (LocalGL3 w)) →
        ∃ B : Finset (LocalGL3 w → ℂ), ∀ G ∈ gl3CyclicSubspace (X.whittakerLoc w),
          (∀ k ∈ Uw, ∀ g : LocalGL3 w, G (g * k) = G g) → G ∈ Submodule.span ℂ (B : Set (LocalGL3 w → ℂ)))
    (hcent : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w →
      (∀ z : (w.adicCompletion ℚ)ˣ, ‖((NumberField.TateGlobal.localChar X.centralChar w z : ℂˣ) : ℂ)‖ = 1) ∧
      ∀ (t : (w.adicCompletion ℚ)ˣ) (h : LocalGL3 w),
        X.whittakerLoc w (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) =
          ((NumberField.TateGlobal.localChar X.centralChar w t : ℂˣ) : ℂ) * X.whittakerLoc w h) :
    ∃ lam : ℂ, lam ≠ 0 ∧
      ∀ W ∈ gl3CyclicSubspace (X.whittakerLoc p), ∀ b : ℕ,
            (∀ w ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ K p,
          2 * (Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal * b) + 1 ≤
            LanglandsTunnell.TateLocal.conductorExponentAt K w (NumberField.TateGlobal.localChar μ w)) →
        ∀ (η : (p.adicCompletion ℚ)ˣ →* ℂˣ) (cη : ℕ),
          LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p η cη → cη ≤ b →
          ∀ ηA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, LanglandsTunnell.Converse.IsAdmissibleTwist ℚ ηA →
            NumberField.TateGlobal.localChar ηA p = η →
            LanglandsTunnell.Converse.IsAdmissibleTwist K
              (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) →
            ∀ g : LocalGL3 p,
              letI := LanglandsTunnell.TateLocal.localBorel ℚ p
              ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
                IsLocalZeta30ConvergentAbove p (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ p)))
                  W η g σ₀ ∧
                (∀ s : ℂ, σ₀ < s.re →
                  localZeta30 p (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ p))) W η s g *
                    Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                  Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
                IsLocalZeta31ConvergentAbove p (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ p))) (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ p) (dualWhittakerFn3 W) η⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
                (∀ s : ℂ, σ₁ < (1 - s).re →
                  localZetaDual31 p (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ p))) (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ p)
                    W η (1 - s) g * Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                  Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s) *
                    (lam *
                      (∏ᶠ w ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ K p,
                        ((NumberField.TateGlobal.localChar
                          (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w (-1) : ℂˣ) : ℂ)) *
                      (∏ᶠ w ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ K p,
                        (LanglandsTunnell.TateLocal.stdRootNumberAt K w
                            (NumberField.TateGlobal.localChar
                              (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w) *
                          (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^
                            (LanglandsTunnell.Converse.pinnedExp K
                                (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w))))) := by sorry
