-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_localZeta31_fe_one_inducedEulerPoly_rational_of_isCubicInductionDataOn_of_isRamifiedIn
-- name    : LanglandsTunnell.CubicInduction.exists_localZeta31_fe_one_inducedEulerPoly_rational_of_isCubicInductionDataOn_of_isRamifiedIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/a85d989e-c1a7-5fd1-8e90-ceeea8524c80
-- title:
--   Local zeta functional equation at a ramified place
-- statement:
--   The setting is a cubic field and an idele class character of it, together with cubic-induction data on $\mathrm{GL}_3/\mathbb{Q}$.
--
--   **Objects.** $K$ is a number field with an integral algebra structure of $\mathcal{O}_{\mathbb{Q}}$ on $\mathcal{O}_K$ and $\operatorname{finrank}_{\mathbb{Q}} K = 3$ (`hdeg`). $\psi$ is an additive character of the adele ring of $\mathbb{Q}$ and `hψ` asserts `IsGlobalAddChar`: $\psi$ is trivial on principal adeles, continuous and non-trivial. $\mu$ is a character of the idele group of $K$ and `hμ` asserts `IsAdmissibleTwist`: $\mu$ is trivial on principal ideles, continuous and unitary.
--
--   **Archimedean parameters of $\mu$.** Functions $uR, aR$ on the real places and $uC, kC$ on the complex places of $K$ (values in $\mathbb{C}$, $\mathbb{Z}/2$, $\mathbb{C}$, $\mathbb{Z}$) are such that (`huR`, `huC`) for every real place $w$ the local component of $\mu$ at $w$ is $x\mapsto |x|^{m_w u_R(w)}(x/|x|)^{a_R(w)}$, with $a_R(w)$ read as the integer representative of its class, and for every complex place $w$ it is $x\mapsto |x|^{m_w u_C(w)}(x/|x|)^{k_C(w)}$, where $m_w$ is the multiplicity of $w$.
--
--   **Level and non-descent.** `hlev`: at every finite place $v$ of $\mathbb{Q}$ the local component `psiLoc ψ v` has `addCharLevel` equal to $0$, i.e. the largest $n$ for which the character is trivial on $\{x : |x|_v \le \exp n\}$ is $0$. `hns`: there is no admissible twist $\eta$ of $\mathbb{Q}$ with $\mu(\varpi_{\mathfrak{P}}) = \eta(\varpi_{v})^{f(\mathfrak{P}/v)}$ for every prime $\mathfrak{P}$ of $K$ at which $\mu$ is unramified and whose trace $v = \mathfrak{P}\cap\mathcal{O}_{\mathbb{Q}}$ carries $\eta$ unramified; that is, $\mu$ does not arise from a character of $\mathbb{Q}$ in this sense.
--
--   **Carrier data and the bad set.** $D$ is a subset of the adelic $\mathrm{GL}_2$ of $\mathbb{Q}$, $U$ assigns to each ideal of $\mathcal{O}_{\mathbb{Q}}$ a subgroup of that group, and `gen` assigns an element to each finite place; these enter only through `productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)`, the carrier pins with the Borel structure and adelic Haar measure on adelic $\mathrm{GL}_2$, central subgroup $\top$, level subgroups $U$, Hecke generators `gen`, and the adelic additive Haar measure conditioned on the adelic box. $S$ is a finite set of finite places of $\mathbb{Q}$ with `hS`: $w \in S$ exactly when $w$ is a bad place, i.e. either ramified in $K$ (some prime above $w$ has ramification index $\ne 1$) or twist-ramified above $w$.
--
--   **The data $X$.** $X$ is a `CubicInductionData`: a form $X.\mathrm{form}$ on adelic $\mathrm{GL}_3$, a global Whittaker function, local Whittaker functions $X.\mathrm{whittakerLoc}\,v$ on $\mathrm{GL}_3$ of each completion, an archimedean Whittaker function, a central character, and a dual Whittaker function. The hypothesis `hX` asserts `IsCubicInductionDataOn` for $K$, the above pins, $\psi$, $\mu$ and $S$ (twenty-two clauses, summarised here): left invariance of the form under $\mathrm{GL}_3(\mathbb{Q})$, the central transformation law by $X.\mathrm{centralChar}$ together with the fact that this character is trivial on principal ideles, cuspidality along the two maximal parabolics $P_{21}$ and $P_{12}$, identification of $X.\mathrm{whittaker}$ with the $\psi$-Whittaker transform of the form and its $\psi$-Whittaker law, the mirabolic Fourier expansion recovering the form, the local $\psi_v$-Whittaker laws, factorisation of the global Whittaker function as the archimedean function times the finite local factors over any finite set containing $S$ outside which the components are integral, induced-spherical behaviour off $S$ with coefficients `inducedCoeff K μ`, invariance under the congruence subgroup of level `inducedLevelAt K μ v` at places off $S$ unramified in $K$, Whittaker multiplicity one, moderate growth, $K$-finiteness of the archimedean Whittaker function, iota moments and a Whittaker half-plane bound, and the corresponding clauses for $X.\mathrm{dualWhittaker}$ relative to $\psi^{-1}$ and the dual form.
--
--   **Analytic hypotheses on $X$.** `hcont`, `hcontW`, `hcontW'`: continuity of the form, the Whittaker function and the dual Whittaker function. `hW`, `hW'`: both Whittaker functions are gauge majorised, i.e. vanish outside a root level and satisfy, for every $N$, a bound $C/(\text{root size product}^t (1+\text{arch root sum})^N)$. `hne`: the archimedean Whittaker function is not identically zero.
--
--   `hatS` gives, at each $w\in S$, four clauses: the normalisation $X.\mathrm{whittakerLoc}\,w(1)=1$; a cyclicity clause, that every non-zero $F$ in the cyclic subspace generated by $X.\mathrm{whittakerLoc}\,w$ has $X.\mathrm{whittakerLoc}\,w$ in the cyclic subspace generated by $F$; smoothness, the existence of an open subgroup $U_w$ of $\mathrm{GL}_3$ of the completion under which $X.\mathrm{whittakerLoc}\,w$ is right invariant; and admissibility, that for every open subgroup $U_w$ the right $U_w$-invariant vectors of the cyclic subspace lie in the span of a finite set.
--
--   `hcent` requires, at each $w\in S$, that the local component of $X.\mathrm{centralChar}$ at $w$ be unitary and that $X.\mathrm{whittakerLoc}\,w$ transform by it under scalar matrices. `hωcond` requires, at each finite place $v$ of $\mathbb{Q}$ not ramified in $K$, a conductor exponent $a \le$ `inducedLevelAt K μ v` $= \sum_{\mathfrak{P}\mid v} f(\mathfrak{P}/v)\,a(\mu_{\mathfrak{P}})$ for the local component of $X.\mathrm{centralChar}$ at $v$.
--
--   **Archimedean splitting and measures.** $E$ is a homomorphism from the units of the infinite adeles to the ideles with (`hE`) infinite part the given unit and finite part $1$. A non-zero rational $a$ is fixed, $a_\infty$ is the infinite-adelic unit it determines (`haInf`), $\psi_\infty$ is the standard archimedean character translated by $a$ (`hpsiInf`), and `hψinf` asserts that the restriction of $\psi$ along the inclusion of the infinite adeles is $\psi_\infty$. With measurable and Borel structures on the infinite adeles and their units, $\nu_{\mathrm{add}}$ is $|a|^{1/2}$ times the pushforward of Lebesgue measure under the inverse of the identification with the mixed space (`hν_add`), and $\nu_{\mathrm{mul}}$ is a Haar measure on the units.
--
--   **The archimedean package `hArch`** (five groups of clauses, summarised here): continuity of $X.\mathrm{whittakerArch}$ with a rapid-decay bound in the archimedean root coordinates; the $\psi_\infty$-Whittaker law; the central transformation law by $X.\mathrm{centralChar}\circ E$; and, for every admissible twist $\sigma$ of $\mathbb{Q}$ with archimedean parameters $(t,e)$ at all real places and every $g_\infty \in \mathrm{GL}_3$ of the infinite adeles, the existence of an entire function $P$ such that the $\mathrm{GL}_3\times\mathrm{GL}_1$ archimedean zeta integral `archZeta30` of the right translate of $X.\mathrm{whittakerArch}$ by $g_\infty$ against $\sigma\circ E$ converges in a right half-plane and equals $P(s)$ times the archimedean factor of the L-datum `heckeDatum K μ` with parameters $(uR+t, aR+e, uC+t, kC)$, that $P$ admits exponential vertical bounds in every vertical strip, that the product of $P$ with that archimedean factor decays faster than any power of $|\operatorname{Im} s|$ in every strip, and that the dual integral `archZetaDual31` (formed with $\nu_{\mathrm{mul}}$, $\nu_{\mathrm{add}}$ and the dual Whittaker function at `weylPrime3 * transposeInv3 1`) converges and satisfies, for $\operatorname{Re}(1-s)$ large, the functional equation with constant the product over real places of $K$ of `signEpsilon (aR + e)`, the product over complex places of $i^{|kC|}$, the product of `lambdaArch K w` over all infinite places of $K$, the factor $X.\mathrm{centralChar}(E a_\infty)\,\sigma(E a_\infty)^3$, the factor $|a|^{3(s-1/2)}$, $P(s)$, and the dual archimedean factor of the same Hecke datum at $1-s$; finally the existence of some admissible twist $\sigma$ and some $s$ with `archZeta30` of $X.\mathrm{whittakerArch}$ against $\sigma\circ E$ non-zero at $s$.
--
--   **The place $v$.** $v$ is a finite place of $\mathbb{Q}$ with $v\in S$ (`hv`) which is ramified in $K$ (`hram`). The natural number $\ell$ satisfies (`hℓ`) $\ell = \sum_{\mathfrak{P}\mid v} f(\mathfrak{P}/v)\cdot \mathrm{pinnedExp}_K(\mu,\mathfrak{P})$, the sum over the fibre of $v$ in $K$, where $\mathrm{pinnedExp}$ is the conductor exponent of the local component of $\mu$ at $\mathfrak{P}$ plus the level of the standard local additive character at $\mathfrak{P}$. Finally `harch` provides some $g_\infty$ and some admissible twist $\sigma$ of $\mathbb{Q}$ with archimedean parameters $(t,e)$ at all real places satisfying $(-1)^e = 1$, such that for every $\sigma_0$ there is $s$ with $\operatorname{Re} s > \sigma_0$ and `archZeta30` of the $g_\infty$-translate of $X.\mathrm{whittakerArch}$ against $\sigma\circ E$ non-zero at $s$; that is, the archimedean zeta integral does not vanish identically arbitrarily far to the right.
--
--   **Conclusion.** There is a non-zero complex number $\varepsilon$ (independent of the group variable) such that for every $g \in \mathrm{GL}_3$ of the completion at $v$ there exist a function $P : \mathbb{C}\to\mathbb{C}$ and real numbers $\sigma_0,\sigma_1$, the local completion being equipped with its Borel structure, with the following five properties, where $q =$ `Ideal.absNorm v.asIdeal`:
--
--   1. $P$ is rational in $q^{-s}$ up to a monomial: there are polynomials $Q, R$ and $m\in\mathbb{N}$ with $R \ne 0$ and $P(s)\,R(q^{-s}) = Q(q^{-s})\,q^{ms}$ for all $s$.
--
--   2. The local $\mathrm{GL}_3\times\mathrm{GL}_1$ zeta integrand for $X.\mathrm{whittakerLoc}\,v$, the trivial character $1$ and the point $g$, taken against the multiplicative measure obtained from the self-dual additive Haar measure at $v$ by `mulMeasure` and restriction to the units, is integrable for $\operatorname{Re} s > \sigma_0$.
--
--   3. For $\operatorname{Re} s > \sigma_0$,
--   $$\mathrm{localZeta30}(s,g) = \bigl(\mathrm{inducedEulerPoly}\ \mathbb{Q}\ (\mathrm{inducedCoeff}\ K\ \mu)\ v\ \text{evaluated at } q^{-s}\bigr)^{-1}\,P(s),$$
--   the induced Euler polynomial being the product of the induced factors over the primes of $K$ above $v$, with coefficients $\mu(\varpi_{\mathfrak{P}})$ at primes where $\mu$ is unramified and $0$ elsewhere.
--
--   4. The corresponding dual integrand, formed from `dualWhittakerFn3 (X.whittakerLoc v)` at the point `weylPrime3 * transposeInv3 g` with the product of that multiplicative measure and the self-dual additive measure, is integrable for $\operatorname{Re} s > \sigma_1$.
--
--   5. For $\operatorname{Re}(1-s) > \sigma_1$,
--   $$\mathrm{localZetaDual31}(1-s,g) = \bigl(\mathrm{inducedEulerPoly}\ \mathbb{Q}\ (\mathrm{inducedCoeff}\ K\ \mu^{-1})\ v\ \text{at } q^{-(1-s)}\bigr)^{-1}\cdot\bigl(\varepsilon\, q^{\ell(1/2-s)}\bigr)\,P(s),$$
--   with the induced Euler polynomial now formed from the inverse character $\mu^{-1}$.
--
--   Thus the same function $P$ serves both identities, the Euler denominators are those of the induced (automorphically induced) Euler factors of $\mu$ and $\mu^{-1}$ at $v$, and the root number $\varepsilon$ together with the exponent $\ell$ is the same for all $g$.
--
--   This is the local step, at a finite place of $\mathbb{Q}$ ramified in the cubic field $K$, of the converse-theorem analysis of the automorphic induction of an idele class character from a cubic field to $\mathrm{GL}_3/\mathbb{Q}$: it extracts from the global functional equations a $g$-independent rational factor and identifies the local zeta and dual zeta integrals of the local Whittaker function with the induced Euler factors of $\mu$ and $\mu^{-1}$, up to a single root number and the shift $q^{\ell(1/2-s)}$ with $\ell$ the conductor exponent of the induced representation at $v$. It is the ramified counterpart of the corresponding statement at places unramified in $K$, and is used in the determination of the local components of the induced data at bad places and in the computation of the global root number.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_localZeta31_fe_one_inducedEulerPoly_rational_of_isCubicInductionDataOn_of_isRamifiedIn.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_RSCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal MeasureTheory LanglandsTunnell.RankinSelberg
  LanglandsTunnell.CubicLambda

open scoped Classical in

theorem LanglandsTunnell.CubicInduction.exists_localZeta31_fe_one_inducedEulerPoly_rational_of_isCubicInductionDataOn_of_isRamifiedIn
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (huR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (huC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (hns : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hS : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w ↔ w ∈ S)
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ
      (S : Set (HeightOneSpectrum (𝓞 ℚ))) X)
    (hcont : Continuous X.form) (hcontW : Continuous X.whittaker) (hcontW' : Continuous X.dualWhittaker)
    (hW : IsGaugeMajorised3 ℚ X.whittaker) (hW' : IsGaugeMajorised3 ℚ X.dualWhittaker)
    (hne : X.whittakerArch ≠ 0)
    (hatS : ∀ w ∈ S, X.whittakerLoc w 1 = 1 ∧
      (∀ F ∈ gl3CyclicSubspace (X.whittakerLoc w), F ≠ 0 → X.whittakerLoc w ∈ gl3CyclicSubspace F) ∧
      (∃ Uw : Subgroup (LocalGL3 w), IsOpen (Uw : Set (LocalGL3 w)) ∧
        ∀ k ∈ Uw, ∀ g : LocalGL3 w, X.whittakerLoc w (g * k) = X.whittakerLoc w g) ∧
      ∀ Uw : Subgroup (LocalGL3 w), IsOpen (Uw : Set (LocalGL3 w)) →
        ∃ B : Finset (LocalGL3 w → ℂ), ∀ F ∈ gl3CyclicSubspace (X.whittakerLoc w),
          (∀ k ∈ Uw, ∀ g : LocalGL3 w, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 w → ℂ)))
    (hcent : ∀ w ∈ S,
      (∀ z : (w.adicCompletion ℚ)ˣ, ‖((localChar X.centralChar w z : ℂˣ) : ℂ)‖ = 1) ∧
      ∀ (t : (w.adicCompletion ℚ)ˣ) (h : LocalGL3 w),
        X.whittakerLoc w (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) =
          ((localChar X.centralChar w t : ℂˣ) : ℂ) * X.whittakerLoc w h)
    (hωcond : ∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsRamifiedIn K v → ∃ a ≤ inducedLevelAt K μ v,
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (localChar X.centralChar v) a)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ, M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
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
    (hArch :
      (Continuous X.whittakerArch ∧ ∃ t : ℕ, ∀ N : ℕ, ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ‖X.whittakerArch (archComponent3 (𝓞 ℚ) ℚ g)‖ ≤
        C / ((∏ w : InfinitePlace ℚ, archRoot₁ ℚ w g * archRoot₂ ℚ w g) ^ t * (1 + archRootSum ℚ g) ^ N)) ∧
      IsGL3PsiWhittakerFn psiInf X.whittakerArch ∧
      (∀ (z : (InfiniteAdeleRing ℚ)ˣ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)),
        X.whittakerArch (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((X.centralChar (E z) : ℂˣ) : ℂ) * X.whittakerArch g) ∧
      (∀ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ →
        ∀ (t : ℂ) (e : ℤ), (∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v t e) →
        ∀ gInf : GL (Fin 3) (InfiniteAdeleRing ℚ), ∃ P : ℂ → ℂ, Differentiable ℂ P ∧
          (∃ σ₀ : ℝ, IsArchZeta30ConvergentAbove ν_mul (fun h => X.whittakerArch (h * gInf)) (σ.comp E) 1 σ₀ ∧
            ∀ s : ℂ, σ₀ < s.re →
              archZeta30 ν_mul (fun h => X.whittakerArch (h * gInf)) (σ.comp E) s 1 =
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
          (∃ σ₁ : ℝ, IsArchZeta31ConvergentAbove ν_mul ν_add (dualWhittakerFn3 (fun h => X.whittakerArch (h * gInf)))
              (σ.comp E)⁻¹ (weylPrime3 * transposeInv3 1) σ₁ ∧
            ∀ s : ℂ, σ₁ < (1 - s).re →
              archZetaDual31 ν_mul ν_add (fun h => X.whittakerArch (h * gInf)) (σ.comp E) (1 - s) 1 =
                (((Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).prod
                    fun w => signEpsilon (aR w.1 w.2 + (e : ZMod 2))) *
                  ((Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).prod
                      fun w => Complex.I ^ (kC w.1 w.2).natAbs) *
                  ∏ w : InfinitePlace K, lambdaArch K w) *
                (((X.centralChar (E aInf) : ℂˣ) : ℂ) * ((σ (E aInf) : ℂˣ) : ℂ) ^ 3) *
                (((|a| : ℝ) : ℂ) ^ (3 * (s - 1 / 2))) *
                P s *
                  (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
                    (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactorDual (1 - s))) ∧
      ∃ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ ∧
        ∃ s : ℂ, archZeta30 ν_mul X.whittakerArch (σ.comp E) s 1 ≠ 0)

    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ∈ S) (hram : IsRamifiedIn K v)
    (ℓ : ℕ) (hℓ : (ℓ : ℤ) = ∑ᶠ w ∈ primeFibre ℚ K v, (v.asIdeal.inertiaDeg' w.asIdeal : ℤ) * LanglandsTunnell.Converse.pinnedExp K μ w)
    (harch : ∃ (gInf : GL (Fin 3) (InfiniteAdeleRing ℚ)) (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ), IsAdmissibleTwist ℚ σ ∧
      (∃ (t : ℂ) (e : ℤ), (∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ σ w t e) ∧ (-1 : ℂ) ^ e = 1) ∧
      ∀ σ₀ : ℝ, ∃ s : ℂ, σ₀ < s.re ∧ archZeta30 ν_mul (fun h => X.whittakerArch (h * gInf)) (σ.comp E) s 1 ≠ 0) :
    ∃ ε : ℂ, ε ≠ 0 ∧
    (∀ g : LocalGL3 v,
      (letI := localBorel ℚ v
       ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
        (∃ (Q R : Polynomial ℂ) (m : ℕ), R ≠ 0 ∧ ∀ s : ℂ,
          P s * R.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) = Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
        IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (X.whittakerLoc v) 1 g σ₀ ∧
        (∀ s : ℂ, σ₀ < s.re →
          localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (X.whittakerLoc v) 1 s g =
            ((inducedEulerPoly ℚ (inducedCoeff K μ) v).eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹ * P s) ∧
        IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
          (selfDualHaarAt ℚ v) (dualWhittakerFn3 (X.whittakerLoc v)) 1 (weylPrime3 * transposeInv3 g) σ₁ ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
              (X.whittakerLoc v) 1 (1 - s) g =
            ((inducedEulerPoly ℚ (inducedCoeff K μ⁻¹) v).eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))))⁻¹ *
              ((ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s))) * P s))) := by sorry
