-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_mul_eq_mul_localZeta30_localZetaDual31_polynomial_of_isCubicInductionDataOn_of_forall_mem_bad
-- name    : LanglandsTunnell.CubicInduction.mul_eq_mul_localZeta30_localZetaDual31_polynomial_of_isCubicInductionDataOn_of_forall_mem_bad
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/bd530cce-99cc-538a-aa34-acb2424319de
-- title:
--   Place separation for local zeta quotients at a bad place
-- statement:
--   Throughout, $K$ is a number field with $[K:\mathbb{Q}]=3$ (hypothesis `_hdeg`), equipped with an algebra structure $\mathcal{O}_{\mathbb{Q}}\to\mathcal{O}_K$ that is integral; $\psi$ is an additive character of the adele ring of $\mathbb{Q}$ which is `IsGlobalAddChar` (trivial on the image of $\mathbb{Q}$, continuous, and non-trivial); and $\mu$ is a character $(\mathbb{A}_K)^\times\to\mathbb{C}^\times$ which is an admissible twist, i.e. trivial on principal ideles, continuous and unitary. A finite place $v$ of $\mathbb{Q}$ is *bad* for the pair $(K,\mu)$ when either some prime of $\mathcal{O}_K$ in the fibre over $v$ has ramification index $\neq 1$, or $\mu$ fails to be unramified at some prime in that fibre. The hypothesis `_hlev` requires $\mathrm{addCharLevel}(\psi_v)=0$ at every place $v$ that is not bad, where $\psi_v$ is the local component of $\psi$; and `_hns` asserts that $\mu$ is not induced from $\mathbb{Q}$ in the following sense: there is no admissible twist $\eta$ of $\mathbb{Q}$ with $\mu(\varpi_{\mathfrak{P}})=\eta(\varpi_{\mathfrak{p}})^{f(\mathfrak{P}/\mathfrak{p})}$ for every prime $\mathfrak{P}$ of $\mathcal{O}_K$ at which $\mu$ is unramified and whose contraction $\mathfrak{p}$ to $\mathcal{O}_{\mathbb{Q}}$ carries $\eta$ unramified, the exponent being the inertia degree, and $\varpi$ denoting the uniformizer idele.
--
--   Carrier data for the $\mathrm{GL}_2$-side are a subset $D$ of $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, a family $U$ of subgroups indexed by ideals of $\mathcal{O}_{\mathbb{Q}}$, and a family $\mathrm{gen}$ of adelic matrices indexed by finite places; they are assembled by `productionPinsOf` into the carrier pins with the Borel $\sigma$-algebra and adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, central subgroup $\top$, and the adelic additive Haar measure conditioned on the adelic box `AdelicBox.adelicBox ℚ`. A finite set $S$ of finite places is given together with `hSbad`: a place is bad precisely when it lies in $S$.
--
--   The datum $X$ is a `CubicInductionData`, that is a tuple consisting of a function `X.form` on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$, its global Whittaker function `X.whittaker`, local Whittaker functions `X.whittakerLoc v` on $\mathrm{GL}_3(\mathbb{Q}_v)$, an archimedean Whittaker function `X.whittakerArch`, a central character `X.centralChar`, and a dual Whittaker function `X.dualWhittaker`. The hypothesis `hX` asserts `IsCubicInductionDataOn` for $X$ relative to the above pins, $\psi$, $\mu$ and $S$; its twenty-two clauses are summarised here as: left invariance of `X.form` under $\mathrm{GL}_3(\mathbb{Q})$ and transformation under the adelic centre by the idele class character `X.centralChar`; cuspidality along the two maximal parabolics $P_{21}$ and $P_{12}$; the identification of `X.whittaker` with the $\psi$-Whittaker coefficient of `X.form`, its $\psi$-Whittaker transformation law, and the summation of its mirabolic translates to `X.form`; the $\psi_v$-Whittaker law for each `X.whittakerLoc v`, factorisation of `X.whittaker` as the archimedean factor times the finitely many local factors over any finite set containing $S$ at which the local components leave the maximal compact; induced-sphericality at places outside $S$ with Hecke eigenvalues prescribed by $\mathrm{inducedCoeff}(K,\mu)$, invariance under the congruence subgroup $K_1$ of level $\mathrm{inducedLevelAt}(\mu,v)$ at unramified places outside $S$, and the Whittaker multiplicity-one normalisation at every place; moderate growth of `X.form`, $K$-finiteness of `X.whittakerArch`, the iota-moment and Whittaker half-plane conditions; and the corresponding clauses for `X.dualWhittaker` with respect to $\psi^{-1}$ and the dual form of `X.form`.
--
--   Analytic hypotheses on $X$: `hcont` the continuity of `X.form`; `hW` and `hW'` gauge majorisation (`IsGaugeMajorised3`) of `X.whittaker` and of `X.dualWhittaker`, i.e. vanishing outside a fixed root level and, for every $N$, a decay bound in terms of the root-size product and the archimedean root sum; `hcontW` and `hcontW'` the continuity of these two functions. A constant $c\in\mathbb{C}$ is given with `hc`: $c$ times the adelic Haar volume of the adelic box equals $1$.
--
--   The hypothesis `hexp` states that `X.form` is non-zero and that at every place $v$ that is not bad and with $\mathrm{addCharLevel}(\psi_v)=0$ one has $W_v(1)=1$ and `HasSphericalTorusValuesAt` for $\mathrm{inducedCoeff}(K,\mu)$ and $W_v=$ `X.whittakerLoc v`, i.e. the prescribed formulae for the values of $W_v$ on the torus points $\mathrm{iotaTorusLocal}$ and on the two-row points in terms of the spherical torus values attached to the induced eigenvalues. The hypothesis `hbad` states, for every finite set $T$ of places: at each bad $v\in T$ there is an open subgroup $U_v\leq \mathrm{GL}_3(\mathbb{Q}_v)$ under which `X.whittakerLoc v` is right invariant; and at each bad $v\in T$, for every non-zero $W$ in the cyclic subspace `gl3CyclicSubspace (X.whittakerLoc v)` spanned by the right translates of `X.whittakerLoc v`, the function `X.whittakerLoc v` itself lies in the cyclic subspace of $W$.
--
--   Further data: a monoid homomorphism $E$ from the units of the infinite adele ring to the idele group with `hE`, stating that $E(u)$ has archimedean part $u$ and trivial finite part; a Haar measure $\nu_{\mathrm{mul}}$ on the units of the infinite adele ring (with Borel structure); and the distinguished place $v\in S$ (hypothesis `hv`), so that $v$ is bad.
--
--   Local hypotheses at the places of $S$: `h1` requires $W_w(1)=1$ for every $w\in S$ with $w\neq v$; `hadm` requires, for each $w\in S$ and each open subgroup $U_w\leq\mathrm{GL}_3(\mathbb{Q}_w)$, a finite set $B$ of functions on $\mathrm{GL}_3(\mathbb{Q}_w)$ such that every element of the cyclic subspace of `X.whittakerLoc w` which is right $U_w$-invariant lies in the $\mathbb{C}$-span of $B$; `hcent` requires, for each $w\in S$, that the local component at $w$ of `X.centralChar` be unitary and that $W_w(\mathrm{scalar}(t)\,h)=\mathrm{localChar}(\mathrm{X.centralChar},w)(t)\,W_w(h)$ for all $t\in\mathbb{Q}_w^\times$ and $h\in\mathrm{GL}_3(\mathbb{Q}_w)$.
--
--   Global integrability hypotheses: `hS` requires, for every admissible twist $\tau$ of $\mathbb{Q}$ and every $g\in\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$, a real $\sigma_0$ such that for $\operatorname{Re} s>\sigma_0$ the function $a\mapsto \mathrm{X.whittaker}(\iota(\mathrm{diag}(a,1))g)\,\tau(a)\,\|a\|^{s-1}$ is integrable for the measure $\nu_S$ of [`NumberField.Idele.productMeasureData ℚ S`](def/NumberField_IdeleProductMeasure.html#L679), where $\iota$ is the embedding $\mathrm{GL}_2\hookrightarrow\mathrm{GL}_3$ in the upper-left corner and $\|\cdot\|$ is the idele norm. The hypothesis `hS'` requires the same integrability, for every admissible twist $\tau$ and every $g$, of the function of $a$ obtained by multiplying $\tau(a)\,\|a\|^{s-1}$ with the product of: the integral over the mixed space of $\mathbb{Q}$ of the dual Whittaker function $\mathrm{dualWhittakerFn}_3(\mathrm{X.whittakerArch})$ evaluated at $\mathrm{arch}(\iota(\mathrm{diag}(a,1)))\cdot u_{21}(y)\cdot\mathrm{arch}(g)$, where $u_{21}$ is the lower unipotent matrix in the $(2,1)$ entry and $y$ is transported to the infinite adeles by the inverse of `InfiniteAdeleRing.ringEquiv_mixedSpace ℚ`; and, for each $v\in S$, the reciprocal of the `selfDualHaarAt ℚ v`-volume of the local integers times the integral over $\mathbb{Q}_v$, against `selfDualHaarAt ℚ v`, of $\mathrm{dualWhittakerFn}_3(\mathrm{X.whittakerLoc}\,v)$ at the local component of $\iota(\mathrm{diag}(a,1))$ times $u_{21}(x)$ times the local component of $g$.
--
--   Under these hypotheses the assertion is the following. Let $\chi:\mathbb{Q}_v^\times\to\mathbb{C}^\times$ be a character such that (i) $\chi$ has a conductor exponent, i.e. there is $c\in\mathbb{N}$ with $\chi$ trivial on the higher units of level $c$ and non-trivial on the higher units of every level $m<c$; and (ii) there exist $g_\infty\in\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q},\infty})$ and an admissible twist $\sigma$ of $\mathbb{Q}$ together with $t\in\mathbb{C}$ and $e\in\mathbb{Z}$ such that at every real infinite place $w$ of $\mathbb{Q}$ the archimedean local component of $\sigma$ is $x\mapsto \|x\|^{\mathrm{mult}(w)\,t}\,(x/\|x\|)^{e}$, such that $\chi(-1)=(-1)^e$, and such that for every $\sigma_0\in\mathbb{R}$ there is $s$ with $\operatorname{Re} s>\sigma_0$ and $\mathrm{archZeta}_{30}$ non-zero at $s$ and the identity matrix, formed with the measure $\nu_{\mathrm{mul}}$, the function $h\mapsto \mathrm{X.whittakerArch}(h\,g_\infty)$ and the character $\sigma\circ E$.
--
--   Then, for all $g,g'\in\mathrm{GL}_3(\mathbb{Q}_v)$, all reals $\sigma_0,\sigma_1$ and all polynomials $P,Q,P_d,Q_d,P',Q',P'_d,Q'_d\in\mathbb{C}[X]$ with $Q,Q',Q_d,Q'_d\neq 0$, the following holds. Write $N=\mathrm{absNorm}(v)$, let $d\mu_v^\times$ be the measure on $\mathbb{Q}_v^\times$ obtained by pulling back along $u\mapsto u$ the measure $|x|^{-1}\,dx$ on $\mathbb{Q}_v\setminus\{0\}$ formed from `selfDualHaarAt ℚ v`, and let $W_v=\mathrm{X.whittakerLoc}\,v$. Assume, for $g$:
--
--   — `IsLocalZeta30ConvergentAbove` at $v$ for $d\mu_v^\times$, $W_v$, $\chi$, $g$ above $\sigma_0$, i.e. integrability of $a\mapsto W_v(\iota(\mathrm{diag}(a,1))g)\chi(a)|a|^{s-1}$ for $\operatorname{Re} s>\sigma_0$;
--
--   — $Q(N^{-s})\cdot \mathrm{localZeta}_{30}(v,d\mu_v^\times,W_v,\chi,s,g)=P(N^{-s})$ for all $s$ with $\operatorname{Re} s>\sigma_0$;
--
--   — `IsLocalZeta31ConvergentAbove` at $v$ for $d\mu_v^\times$, `selfDualHaarAt ℚ v`, the function $\mathrm{dualWhittakerFn}_3(W_v)$, the character $\chi^{-1}$ and the point $w'\,{}^t g^{-1}$ above $\sigma_1$, where $w'=\mathrm{weylPrime}_3$ and ${}^tg^{-1}=\mathrm{transposeInv}_3 g$;
--
--   — $Q_d(N^{-s})\cdot \mathrm{localZetaDual}_{31}(v,d\mu_v^\times,\mathrm{selfDualHaarAt}\,\mathbb{Q}\,v,W_v,\chi,1-s,g)=P_d(N^{-s})$ for all $s$ with $\sigma_1<\operatorname{Re}(1-s)$;
--
--   and assume the four corresponding statements for $g'$ with $P',Q',P'_d,Q'_d$ in place of $P,Q,P_d,Q_d$ and with the same $\sigma_0,\sigma_1$. Then
--   $$P\,P'_d\,Q'\,Q_d = P'\,P_d\,Q\,Q'_d \quad\text{in } \mathbb{C}[X],$$
--   and moreover $P\neq 0$ implies $P_d\neq 0$.
--
--   This is the global step in the extraction of a local functional equation at a bad place $v$ for the $\mathrm{GL}_3\times\mathrm{GL}_1$ zeta integrals of a cubic-induction datum: it says that the ratio of the local zeta integral at $s$ to the dual local zeta integral at $1-s$, read as a rational function of $N(v)^{-s}$ through the given numerators and denominators, is the same at two arbitrary points $g,g'$ of $\mathrm{GL}_3(\mathbb{Q}_v)$, and that a non-vanishing numerator on one side forces one on the other. It is obtained from the global functional equation `exists_entire_eq_globalZeta30_eq_mul_globalZetaDual31_of_isCubicInductionDataOn` together with the unramified comparison of characters and the construction of a global admissible twist matching $\chi$ on the units, and it is used by [`LanglandsTunnell.CubicInduction.exists_forall_exists_mul_eval_eq_of_isCubicInductionDataOn_of_forall_mem_bad_of_addCharLevel`](thm.html#LanglandsTunnell.CubicInduction.exists_forall_exists_mul_eval_eq_of_isCubicInductionDataOn_of_forall_mem_bad_of_addCharLevel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_mul_eq_mul_localZeta30_localZetaDual31_polynomial_of_isCubicInductionDataOn_of_forall_mem_bad.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal MeasureTheory

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in
open scoped Classical in

theorem LanglandsTunnell.CubicInduction.mul_eq_mul_localZeta30_localZetaDual31_polynomial_of_isCubicInductionDataOn_of_forall_mem_bad
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
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSbad : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w ↔ w ∈ S)
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ
      (S : Set (HeightOneSpectrum (𝓞 ℚ))) X)
    (hcont : Continuous X.form) (hW : IsGaugeMajorised3 ℚ X.whittaker) (hW' : IsGaugeMajorised3 ℚ X.dualWhittaker)
    (hcontW : Continuous X.whittaker) (hcontW' : Continuous X.dualWhittaker)
    (c : ℂ) (hc : c * ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ)).toReal : ℂ) = 1)
    (hexp : X.form ≠ 0 ∧ ∀ v, ¬ IsBadPlace K μ v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
        X.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v (X.whittakerLoc v))
    (hbad : ∀ T : Finset (HeightOneSpectrum (𝓞 ℚ)),
      (∀ v ∈ T, IsBadPlace K μ v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
        ∀ k ∈ Uv, ∀ g : LocalGL3 v, X.whittakerLoc v (g * k) = X.whittakerLoc v g) ∧
      (∀ v ∈ T, IsBadPlace K μ v → ∀ W ∈ gl3CyclicSubspace (X.whittakerLoc v), W ≠ 0 →
        X.whittakerLoc v ∈ gl3CyclicSubspace W))
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
    M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ∈ S)
    (h1 : ∀ w ∈ S, w ≠ v → X.whittakerLoc w 1 = 1)
    (hadm : ∀ w ∈ S, ∀ Uw : Subgroup (LocalGL3 w), IsOpen (Uw : Set (LocalGL3 w)) →
      ∃ B : Finset (LocalGL3 w → ℂ), ∀ G ∈ gl3CyclicSubspace (X.whittakerLoc w),
        (∀ k ∈ Uw, ∀ g : LocalGL3 w, G (g * k) = G g) → G ∈ Submodule.span ℂ (B : Set (LocalGL3 w → ℂ)))
    (hcent : ∀ w ∈ S,
      (∀ z : (w.adicCompletion ℚ)ˣ, ‖((TateGlobal.localChar X.centralChar w z : ℂˣ) : ℂ)‖ = 1) ∧
      ∀ (t : (w.adicCompletion ℚ)ˣ) (h : LocalGL3 w),
        X.whittakerLoc w (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) =
          ((TateGlobal.localChar X.centralChar w t : ℂˣ) : ℂ) * X.whittakerLoc w h)
    (hS : ∀ τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ τ → ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ∃ σ₀ : ℝ,
      ∀ s : ℂ, σ₀ < s.re →
        Integrable (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
          X.whittaker (iotaGL (diagUnitGL2 a) * g) * ((τ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1))
          (NumberField.Idele.productMeasureData ℚ S).νS)
    (hS' : ∀ τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ τ → ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ∃ σ₀ : ℝ,
      ∀ s : ℂ, σ₀ < s.re →
        Integrable (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
          (∫ y : mixedEmbedding.mixedSpace ℚ,
              dualWhittakerFn3 X.whittakerArch (archComponent3 (𝓞 ℚ) ℚ (iotaGL (diagUnitGL2 a)) *
                lowerUnipotent21 ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y) * archComponent3 (𝓞 ℚ) ℚ g)) *
            (∏ v ∈ S,
              (letI := LanglandsTunnell.TateLocal.localBorel ℚ v
               ((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set
                 (v.adicCompletion ℚ)) : ℂ)⁻¹ *
                 ∫ x : v.adicCompletion ℚ,
                   dualWhittakerFn3 (X.whittakerLoc v) (componentAt3 (𝓞 ℚ) ℚ v (iotaGL (diagUnitGL2 a)) *
                     lowerUnipotent21 x * componentAt3 (𝓞 ℚ) ℚ v g)
                     ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v))) *
            ((τ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1))
          (NumberField.Idele.productMeasureData ℚ S).νS) :
    ∀ χ : (v.adicCompletion ℚ)ˣ →* ℂˣ,
      (∃ c : ℕ, LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v χ c) →
      (∃ (gInf : GL (Fin 3) (InfiniteAdeleRing ℚ)) (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ), IsAdmissibleTwist ℚ σ ∧ (∃ (t : ℂ) (e : ℤ), (∀ w : InfinitePlace ℚ, w.IsReal →
      IsArchCompAt ℚ σ w t e) ∧ ((χ (-1) : ℂˣ) : ℂ) = (-1 : ℂ) ^ e) ∧ ∀ σ₀ : ℝ, ∃ s : ℂ, σ₀ < s.re ∧
      archZeta30 ν_mul (fun h => X.whittakerArch (h * gInf)) (σ.comp E) s 1 ≠ 0) →
      ∀ (g g' : LocalGL3 v) (σ₀ σ₁ : ℝ) (P Q Pd Qd P' Q' Pd' Qd' : Polynomial ℂ),
        Q ≠ 0 → Q' ≠ 0 → Qd ≠ 0 → Qd' ≠ 0 →
        letI := localBorel ℚ v
        (IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (X.whittakerLoc v) χ g σ₀ ∧
          (∀ s : ℂ, σ₀ < s.re → Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (X.whittakerLoc v) χ s g = P.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) ∧
          IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
            (dualWhittakerFn3 (X.whittakerLoc v)) χ⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
          (∀ s : ℂ, σ₁ < (1 - s).re → Qd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) *
            localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
              (X.whittakerLoc v) χ (1 - s) g = Pd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))) →
        (IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (X.whittakerLoc v) χ g' σ₀ ∧
          (∀ s : ℂ, σ₀ < s.re → Q'.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (X.whittakerLoc v) χ s g' = P'.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) ∧
          IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
            (dualWhittakerFn3 (X.whittakerLoc v)) χ⁻¹ (weylPrime3 * transposeInv3 g') σ₁ ∧
          (∀ s : ℂ, σ₁ < (1 - s).re → Qd'.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) *
            localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
              (X.whittakerLoc v) χ (1 - s) g' = Pd'.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))) →
        (P * Pd' * Q' * Qd = P' * Pd * Q * Qd' ∧ (P ≠ 0 → Pd ≠ 0)) := by sorry
