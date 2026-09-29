-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_localZeta31_fe_one_inducedEulerPoly_rational_of_isCubicInductionDataOn_of_not_isRamifiedIn
-- name    : LanglandsTunnell.CubicInduction.exists_localZeta31_fe_one_inducedEulerPoly_rational_of_isCubicInductionDataOn_of_not_isRamifiedIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/d433c644-3055-5744-8d80-ecf0e1adbda9
-- title:
--   Local functional equation at a bad place unramified in K
-- statement:
--   Throughout, $K$ is a number field of degree $3$ over $\mathbb{Q}$ (hypothesis `hdeg`: $\operatorname{finrank}_{\mathbb{Q}} K = 3$), equipped with an integral algebra structure of $\mathcal{O}_{\mathbb{Q}}$ on $\mathcal{O}_K$; $\psi$ is an additive character of the adele ring of $\mathbb{Q}$ with values in $\mathbb{C}$ which is global in the sense of `IsGlobalAddChar` (trivial on the image of $\mathbb{Q}$, continuous, and non-trivial); and $\mu$ is a character of the idele group of $K$ which is an admissible twist, i.e. trivial on principal ideles, continuous, and of absolute value $1$ everywhere.
--
--   *Archimedean parameters of $\mu$* (`uR`, `aR`, `uC`, `kC`, `huR`, `huC`): complex numbers $u_w$ and classes $a_w \in \mathbb{Z}/2$ are given at the real places $w$ of $K$, and complex numbers $u_w$ together with integers $k_w$ at the complex places, such that at every real place the local component of $\mu$ is $x \mapsto \|x\|^{m_w u_w}(x/\|x\|)^{a_w}$ with exponent the representative $(a_w)_{\mathrm{val}} \in \mathbb{Z}$, and at every complex place it is $x \mapsto \|x\|^{m_w u_w}(x/\|x\|)^{k_w}$, in the sense of `IsArchCompAt`.
--
--   *Level and non-base-change hypotheses*: `hlev` requires $\operatorname{addCharLevel}(\psi_v) = 0$ at every finite place $v$ of $\mathbb{Q}$, where $\psi_v$ is the local component `psiLoc` of $\psi$; `hns` requires that there be no admissible twist $\eta$ of $\mathbb{Q}$ with $\mu(\varpi_{\mathfrak{P}}) = \eta(\varpi_{v})^{f(\mathfrak{P}/v)}$ for all primes $\mathfrak{P}$ of $K$ at which $\mu$ is unramified and whose trace $v = \mathfrak{P} \cap \mathcal{O}_{\mathbb{Q}}$ carries an unramified $\eta$, the exponent being the inertia degree `inertiaDeg'`; here $\varpi$ denotes the uniformizer ideles `uniformizerIdele`.
--
--   *Carrier data and bad set*: $D$ is a subset of $\mathrm{GL}_2$ of the adeles of $\mathbb{Q}$, $U$ assigns a subgroup to each ideal of $\mathcal{O}_{\mathbb{Q}}$, $\mathrm{gen}$ assigns an adelic $\mathrm{GL}_2$ element to each finite place, and $S$ is a finite set of finite places characterised by `hS` as exactly the bad places of $(K,\mu)$, that is those $w$ which either ramify in $K$ or lie below a prime where $\mu$ is twist-ramified.
--
--   *The cubic induction datum*: $X$ is a `CubicInductionData`, consisting of a form `X.form` on $\mathrm{GL}_3$ of the adeles of $\mathbb{Q}$, a Whittaker function `X.whittaker`, local Whittaker functions `X.whittakerLoc v` on $\mathrm{GL}_3$ of the completion at each finite $v$, an archimedean Whittaker function `X.whittakerArch`, a central character `X.centralChar`, and a dual Whittaker function `X.dualWhittaker`. The hypothesis `hX` asserts `IsCubicInductionDataOn` for $K$, the pins `productionPinsOf` built from $D$, $U$, $\mathrm{gen}$ and the adelic box (Borel structures, adelic Haar measure on $\mathrm{GL}_2$, full centre, and the additive adelic Haar measure conditioned on the box), the character $\psi$, the character $\mu$ and the set $S$; its clauses (summarised here) require: left invariance of `X.form` under the rational points, its transformation under central scalars by `X.centralChar`, which is trivial on principal ideles, cuspidality along the two maximal parabolics $P_{21}$ and $P_{12}$, the identification of `X.whittaker` with the $\psi$-Whittaker integral of `X.form`, the $\psi$-Whittaker transformation law under upper unipotents, the mirabolic Fourier expansion of `X.form` by `X.whittaker`, the local $\psi_v$-Whittaker laws for the `X.whittakerLoc v`, factorisation of `X.whittaker` as `X.whittakerArch` at the archimedean component times the product of the local factors over any finite set containing $S$ outside which the components are integral, sphericity of induced type at every $v \notin S$, right invariance under the congruence subgroup of level `inducedLevelAt K μ v` at every $v \notin S$ unramified in $K$, local Whittaker multiplicity one, moderate growth of `X.form`, $K$-finiteness of `X.whittakerArch`, iota moments and a Whittaker half-plane condition, together with the corresponding clauses for `X.dualWhittaker` relative to $\psi^{-1}$ and the dual form.
--
--   *Analytic and local regularity hypotheses*: `hcont`, `hcontW`, `hcontW'` are continuity of `X.form`, `X.whittaker` and `X.dualWhittaker`; `hW`, `hW'` are the gauge majorisation `IsGaugeMajorised3` of `X.whittaker` and `X.dualWhittaker` (support inside a root level and rapid decay there); `hne` is `X.whittakerArch ≠ 0`. The hypothesis `hatS` requires, at each $w \in S$, four things: $W_w(1) = 1$; every non-zero element $F$ of the cyclic subspace generated by $W_w$ under right translation generates $W_w$ back; $W_w$ is right invariant under some open subgroup; and for every open subgroup $U_w$ there is a finite set $B$ of functions spanning all $U_w$-right-invariant elements of the cyclic subspace of $W_w$. The hypothesis `hcent` requires, at each $w \in S$, that the local component of `X.centralChar` be of absolute value $1$ and that $W_w$ transform by it under the scalar matrices. The hypothesis `hωcond` requires, at every finite $v$ not ramified in $K$, the existence of $a \le$ `inducedLevelAt K μ v` with `HasConductorExponentAt` $a$ for the local component of `X.centralChar` at $v$.
--
--   *Archimedean splitting and measures*: $E$ is a homomorphism from the units of the infinite adeles to the ideles with `hE` stating that the infinite part of $E u$ is $u$ and its finite part is trivial; $a$ is a non-zero rational, $a_\infty$ the corresponding unit of the infinite adele ring (`haInf`), and $\psi_\infty$ the additive character $x \mapsto \psi_{\mathrm{arch}}(a x)$ (`hpsiInf`), which by `hψinf` is the restriction of $\psi$ to the infinite component. The measure $\nu_{\mathrm{add}}$ is $|a|^{1/2}$ times the transport of Lebesgue measure along the inverse of the mixed-space ring equivalence (`hν_add`), and $\nu_{\mathrm{mul}}$ is a Haar measure on the units of the infinite adeles, both spaces carrying Borel structures.
--
--   The hypothesis `hArch` is a conjunction of five groups. First, `X.whittakerArch` is continuous and there is $t \in \mathbb{N}$ such that for every $N$ some $C$ bounds $\|X.\mathrm{whittakerArch}(g_\infty)\|$ by $C$ divided by $(\prod_w \mathrm{archRoot}_1 \cdot \mathrm{archRoot}_2)^t (1 + \mathrm{archRootSum})^N$. Second, `X.whittakerArch` satisfies the $\psi_\infty$-Whittaker law. Third, it transforms under archimedean scalars $z$ by `X.centralChar (E z)`. Fourth, for every admissible twist $\sigma$ of $\mathbb{Q}$, every pair $(t,e) \in \mathbb{C}\times\mathbb{Z}$ describing the archimedean components of $\sigma$ at all real places of $\mathbb{Q}$, and every $g_\infty \in \mathrm{GL}_3$ of the infinite adeles, there exists an entire function $P$ such that: the integral `archZeta30` for the right translate of `X.whittakerArch` by $g_\infty$ and the character $\sigma \circ E$ converges above some $\sigma_0$ and equals, for $\operatorname{Re} s > \sigma_0$, the product of $P(s)$ with the archimedean factor of the $L$-datum `heckeDatum K μ` formed from the shifted parameters $u_w + t$, $a_w + e$ at real places and $u_w + t$, $k_w$ at complex places; $P$ is bounded on vertical strips by $C\exp(A|\operatorname{Im} s|)$; the product of $P$ with that archimedean factor decays faster than any power of $|\operatorname{Im} s|$ in vertical strips; and the dual integral `archZeta31` for the dual Whittaker function, the inverse character and the point `weylPrime3 * transposeInv3 1` converges above some $\sigma_1$, with
--   $$\mathrm{archZetaDual31}(1-s) = \Big(\prod_{w \text{ real}} \mathrm{signEpsilon}(a_w + e)\Big)\Big(\prod_{w \text{ complex}} i^{|k_w|}\Big)\Big(\prod_{w} \mathrm{lambdaArch}\,K\,w\Big) \cdot \mathrm{centralChar}(E a_\infty)\,\sigma(E a_\infty)^3 \cdot |a|^{3(s - 1/2)} \cdot P(s) \cdot \mathrm{archFactorDual}(1-s)$$
--   for $\operatorname{Re}(1-s) > \sigma_1$, the products over the real and complex places of $K$ and `archFactorDual` that of the same shifted `heckeDatum`. Fifth, there is an admissible twist $\sigma$ of $\mathbb{Q}$ and a point $s$ at which `archZeta30` of `X.whittakerArch` against $\sigma \circ E$ at the identity does not vanish.
--
--   Finally, $v$ is a finite place with $v \in S$ and `hram`: $v$ is not ramified in $K$; and `harch` provides some $g_\infty$, some admissible twist $\sigma$ of $\mathbb{Q}$ whose real archimedean parameters are given by a pair $(t,e)$ with $(-1)^e = 1$, such that for every $\sigma_0$ there is $s$ with $\operatorname{Re} s > \sigma_0$ and `archZeta30` of the translate of `X.whittakerArch` by $g_\infty$ against $\sigma \circ E$ non-zero at $s$.
--
--   **Conclusion.** There exists $\varepsilon \in \mathbb{C}$, $\varepsilon \neq 0$, with the following property. Write $q = \mathrm{absNorm}\,v$, let the completion at $v$ carry its Borel structure, let $\mu_v$ be the multiplicative measure obtained by comapping, along the inclusion of units, the measure `mulMeasure` of the self-dual additive Haar measure `selfDualHaarAt ℚ v`, and let $W_v =$ `X.whittakerLoc v`. For every $g \in \mathrm{GL}_3$ of the completion at $v$ there exist a function $P : \mathbb{C} \to \mathbb{C}$ and reals $\sigma_0, \sigma_1$ such that:
--
--   1. $P$ is rational in $q^{-s}$ up to a monomial: there are polynomials $Q, R$ over $\mathbb{C}$ and $m \in \mathbb{N}$ with $R \neq 0$ and $P(s)\,R(q^{-s}) = Q(q^{-s})\,q^{ms}$ for all $s$;
--
--   2. the zeta integral `localZeta30` at $v$ for $\mu_v$, the function $W_v$, the trivial character and the point $g$ converges for $\operatorname{Re} s > \sigma_0$;
--
--   3. for $\operatorname{Re} s > \sigma_0$,
--   $$\mathrm{localZeta30}(s,g) = \big(\mathrm{inducedEulerPoly}\,\mathbb{Q}\,(\mathrm{inducedCoeff}\,K\,\mu)\,v\big)(q^{-s})^{-1}\,P(s),$$
--   the Euler polynomial being the finite product over the primes of $K$ above $v$ of the induced factors built from the coefficients $\mu(\varpi_{\mathfrak{P}})$ at unramified $\mathfrak{P}$ and $0$ otherwise;
--
--   4. the dual integral `localZeta31` at $v$ for $\mu_v$, the additive measure `selfDualHaarAt ℚ v`, the function `dualWhittakerFn3` $W_v$, the trivial character and the point `weylPrime3 * transposeInv3 g` converges above $\sigma_1$;
--
--   5. for every $s$ with $\operatorname{Re}(1-s) > \sigma_1$,
--   $$\mathrm{localZetaDual31}(1-s, g) = \big(\mathrm{inducedEulerPoly}\,\mathbb{Q}\,(\mathrm{inducedCoeff}\,K\,\mu^{-1})\,v\big)\big(q^{-(1-s)}\big)^{-1}\cdot\Big(\varepsilon\, q^{\,\ell_v(1/2 - s)}\Big)\,P(s),$$
--   where $\ell_v =$ `inducedLevelAt K μ v` is the sum over the primes $\mathfrak{P}$ of $K$ above $v$ of the inertia degree of $\mathfrak{P}/v$ times the conductor exponent of the local component of $\mu$ at $\mathfrak{P}$.
--
--   The constant $\varepsilon$ is independent of $g$, while $P$, $\sigma_0$ and $\sigma_1$ may depend on $g$.
--
--   This is the local functional equation, with root number, of the $\mathrm{GL}_3$ zeta integrals of the cubic induction datum at a bad place $v$ that is unramified in $K$: the local factors at $v$ are shown to be those of the induced (Asai/base-change type) Euler polynomial attached to $\mu$, up to a non-zero constant $\varepsilon$ and the expected power of $q$ determined by the induced level. It is used further on in the Langlands–Tunnell converse-theorem argument, both in the analysis of the cyclic subspace and congruence-level behaviour of the local Whittaker function at $v$ and in the determination of the global root number.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_localZeta31_fe_one_inducedEulerPoly_rational_of_isCubicInductionDataOn_of_not_isRamifiedIn.lean

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

theorem LanglandsTunnell.CubicInduction.exists_localZeta31_fe_one_inducedEulerPoly_rational_of_isCubicInductionDataOn_of_not_isRamifiedIn
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

    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ∈ S) (hram : ¬ IsRamifiedIn K v)
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
              ((ε * (Ideal.absNorm v.asIdeal : ℂ) ^ ((inducedLevelAt K μ v : ℂ) * (1 / 2 - s))) * P s))) := by sorry
