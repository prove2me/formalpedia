-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_eval_mul_eq_finprod_rootNumber_mul_eval_of_forall_localZeta31_fe_one_of_isCubicInductionDataOn_of_addCharLevel
-- name    : LanglandsTunnell.CubicInduction.eval_mul_eq_finprod_rootNumber_mul_eval_of_forall_localZeta31_fe_one_of_isCubicInductionDataOn_of_addCharLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/c54d684b-06de-555d-9a0c-76c9a6c20a24
-- title:
--   Explicit root number in the GL₃ functional equation at v
-- statement:
--   Fix a number field $K$ with $[K:\mathbb{Q}]=3$ (hypothesis `_hdeg`), its ring of integers being an integral $\mathcal{O}_{\mathbb{Q}}$-algebra; an additive character $\psi$ of the adele ring of $\mathbb{Q}$ with values in $\mathbb{C}$ which is global in the sense of `IsGlobalAddChar` (trivial on principal adeles, continuous, and $\neq 1$); and a character $\mu:(\mathbb{A}_K)^\times\to\mathbb{C}^\times$ which is an admissible twist, i.e. trivial on $K^\times$, continuous and unitary.
--
--   Two further global conditions are imposed on this pair. First (`_hlev`), at every finite place $v$ of $\mathbb{Q}$ which is not a bad place for $(K,\mu)$ — bad meaning ramified in $K$ or twist-ramified above — the local component $\psi_v$ has `addCharLevel` equal to $0$. Second (`_hns`), there is no admissible twist $\eta$ of $\mathbb{Q}$ such that for every prime $\mathfrak{P}$ of $\mathcal{O}_K$ at which $\mu$ is unramified and whose prime $\mathfrak{p}$ below carries $\eta$ unramified, $\mu$ of the uniformiser idele at $\mathfrak{P}$ equals $\eta$ of the uniformiser idele at $\mathfrak{p}$ raised to the inertia degree $f(\mathfrak{P}/\mathfrak{p})$; that is, $\mu$ is not obtained by base change from $\mathbb{Q}$ in this sense.
--
--   The carrier data consist of a subset $D$ of $\mathrm{GL}_2$ of the adeles of $\mathbb{Q}$, an assignment $U$ of subgroups of that group to ideals of $\mathcal{O}_{\mathbb{Q}}$, and an assignment `gen` of elements to finite places; they are packaged by `productionPinsOf` together with the adelic box `AdelicBox.adelicBox ℚ`, whose conditional adelic Haar measure is the measure entering the Whittaker coefficient. A finite set $S$ of finite places of $\mathbb{Q}$ is assumed (`hSbad`) to consist exactly of the bad places.
--
--   The analytic object is a `CubicInductionData` $X$, consisting of a function `X.form` on $\mathrm{GL}_3$ of the adeles, its Whittaker function `X.whittaker`, local Whittaker functions `X.whittakerLoc v` on $\mathrm{GL}_3(\mathbb{Q}_v)$, an archimedean Whittaker function `X.whittakerArch`, a central character `X.centralChar` and a dual Whittaker function `X.dualWhittaker`. The hypothesis `hX` asserts `IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ S X`: its clauses (summarised here) require left invariance of `X.form` under the rational points of $\mathrm{GL}_3$, transformation under adelic scalars by the idele class character `X.centralChar`, cuspidality along the two maximal parabolics $P_{21}$, $P_{12}$, the identification of `X.whittaker` with the $\psi$-Whittaker coefficient of `X.form` together with the $\psi$-Whittaker transformation law and the mirabolic expansion summing `X.whittaker` back to `X.form`, the local $\psi_v$-Whittaker laws and the factorisation of `X.whittaker` as `X.whittakerArch` at the archimedean component times a finite product of the `X.whittakerLoc v`, induced sphericity at the places outside $S$ for the coefficient system `inducedCoeff K μ` (whose value at $\mathfrak{P}$ is $\mu$ of the uniformiser idele at $\mathfrak{P}$ when $\mu$ is unramified there, and $0$ otherwise), invariance under the congruence subgroups `congruenceK1` of level `inducedLevelAt K μ v` outside $S$ at places unramified in $K$, Whittaker multiplicity one at every place, moderate growth of `X.form`, $K$-finiteness of `X.whittakerArch`, the iota-moment and Whittaker half-plane conditions, and the corresponding statements for the dual: `X.dualWhittaker` is the $\psi^{-1}$-Whittaker coefficient of the dual form, satisfies the $\psi^{-1}$-Whittaker law, expands mirabolically to the dual form, and has iota moments and a Whittaker half-plane.
--
--   Regularity and normalisation hypotheses: `X.form` is continuous (`hcont`); `X.whittaker` and `X.dualWhittaker` are gauge-majorised in the sense of `IsGaugeMajorised3` (`hW`, `hW'`) and continuous (`hcontW`, `hcontW'`); a constant $c\in\mathbb{C}$ is given with $c$ times the real volume of the adelic box equal to $1$ (`hc`). The hypothesis `hexp` states that `X.form` is non-zero and that at every place $v$ which is not bad and where $\psi_v$ has level $0$ one has `X.whittakerLoc v 1 = 1` and `HasSphericalTorusValuesAt (inducedCoeff K μ) v (X.whittakerLoc v)`, the explicit spherical values on the torus and on two-row points. The hypothesis `hbad` states, for every finite set $T$ of places, that at each bad $v\in T$ the function `X.whittakerLoc v` is right invariant under some open subgroup of $\mathrm{GL}_3(\mathbb{Q}_v)$, and that `X.whittakerLoc v` lies in the cyclic subspace `gl3CyclicSubspace W` of every non-zero $W$ in its own cyclic subspace.
--
--   A place $v\in S$ is singled out (`hv`). At the remaining places of $S$ the normalisation `X.whittakerLoc w 1 = 1` holds (`h1`). For every $w\in S$ and every open subgroup $U_w$ of $\mathrm{GL}_3(\mathbb{Q}_w)$ there is a finite set $B$ of functions whose $\mathbb{C}$-span contains all $U_w$-right-invariant elements of `gl3CyclicSubspace (X.whittakerLoc w)` (`hadm`, admissibility). For every $w\in S$ the local central character `TateGlobal.localChar X.centralChar w` is unitary and `X.whittakerLoc w` transforms by it under scalar matrices (`hcent`), and $\psi_w$ has level $0$ (`hψw`).
--
--   Two global integrability hypotheses are imposed. `hS`: for every admissible twist $\tau$ of $\mathbb{Q}$ and every $g\in\mathrm{GL}_3$ of the adeles there is $\sigma_0$ such that for $\operatorname{Re} s>\sigma_0$ the function $a\mapsto X.\mathrm{whittaker}\big(\iota(\mathrm{diag}(a,1))g\big)\,\tau(a)\,\|a\|^{s-1}$ is integrable for the $S$-part measure $\nu_S$ of [`NumberField.Idele.productMeasureData ℚ S`](def/NumberField_IdeleProductMeasure.html#L679), where $\|\cdot\|$ is the idele norm. `hS'`: the same for the dual integrand, namely the product of the archimedean integral of `dualWhittakerFn3 X.whittakerArch` along the lower unipotent direction at $\iota(\mathrm{diag}(a,1))$ and the archimedean component of $g$, with, for each $v\in S$, the integral of `dualWhittakerFn3 (X.whittakerLoc v)` along `lowerUnipotent21` against the self-dual Haar measure at $v$, normalised by the inverse volume of the local integers, times $\tau(a)\|a\|^{s-1}$.
--
--   At the chosen place $v$ it is assumed that $v$ is unramified in $K$ (`hKv`), that $\psi_v$ has level $0$ (`hψv`), and moreover (`hψinv`) that $\psi_v$ is the inverse $(\psi_{\mathbb{Q},v}^{\mathrm{std}})^{-1}$ of the standard local additive character. A monoid homomorphism $E$ from the units of the infinite adeles of $\mathbb{Q}$ to the ideles is given which splits the infinite part: the infinite part of $E(u)$ is $u$ and its finite part is $1$ (`hE`); the units of the infinite adeles carry a Borel measurable structure and a Haar measure $\nu_{\mathrm{mul}}$. The archimedean non-vanishing hypothesis `harch` asserts the existence of $g_\infty\in\mathrm{GL}_3$ of the infinite adeles and an admissible twist $\sigma$ of $\mathbb{Q}$ such that, for some $t\in\mathbb{C}$ and $e\in\mathbb{Z}$, $\sigma$ has archimedean component type $(t,e)$ at every real infinite place of $\mathbb{Q}$ in the sense of `IsArchCompAt` and the value of the trivial character of $(\mathbb{Q}_v)^\times$ at $-1$ equals $(-1)^e$ (so $e$ is even), and such that for every $\sigma_0$ there is $s$ with $\operatorname{Re} s>\sigma_0$ and $\mathrm{archZeta30}\,\nu_{\mathrm{mul}}\,(h\mapsto X.\mathrm{whittakerArch}(h\,g_\infty))\,(\sigma\circ E)\,s\,1\neq 0$.
--
--   Finally, non-zero polynomials $R_1,R_2\in\mathbb{C}[X]$ and an integer $m$ are given together with the rational functional-equation datum `hFE1`: writing $N=N(v)$ for the absolute norm of $v$, for every $g\in\mathrm{GL}_3(\mathbb{Q}_v)$ there exist polynomials $Q_1,Q_2$ with $Q_2\neq 0$, an integer $n$ and reals $\sigma_0,\sigma_1$ such that the trivial-character zeta integral `localZeta30` of `X.whittakerLoc v`, taken for the multiplicative measure obtained from the self-dual Haar measure at $v$, converges for $\operatorname{Re} s>\sigma_0$ and satisfies there
--   $$\mathrm{localZeta30}(s,g)\cdot Q_2(N^{-s}) = Q_1(N^{-s})\,N^{ns},$$
--   while the dual integral `IsLocalZeta31ConvergentAbove` for `dualWhittakerFn3 (X.whittakerLoc v)` with trivial character at `weylPrime3 * transposeInv3 g` converges above $\sigma_1$ and, for $\operatorname{Re}(1-s)>\sigma_1$,
--   $$\mathrm{localZetaDual31}(1-s,g)\cdot\big(Q_2(N^{-s})R_2(N^{-s})\big) = R_1(N^{-s})\,Q_1(N^{-s})\,N^{(m+n)s}.$$
--
--   The conclusion is the identity, valid for every $s\in\mathbb{C}$,
--   $$R_1(N^{-s})\,N^{ms}\,P^{\vee}\big(N^{-(1-s)}\big) = \Big(\prod_{w\mid v}\mu_w(-1)\Big)\Big(\prod_{w\mid v}\varepsilon_{K,w}(\mu_w)\Big)\,N^{\ell(1/2-s)}\,P(N^{-s})\,R_2(N^{-s}),$$
--   where both products are `finprod`s over the set `primeFibre ℚ K v` of primes $w$ of $\mathcal{O}_K$ lying under $v$, $\mu_w=\mathrm{localChar}\,\mu\,w$, $\varepsilon_{K,w}(\mu_w)=\mathrm{stdRootNumberAt}\,K\,w\,\mu_w$ is the standard local epsilon factor at $s=1/2$, $P=\mathrm{inducedEulerPoly}\,\mathbb{Q}\,(\mathrm{inducedCoeff}\,K\,\mu)\,v$ and $P^{\vee}=\mathrm{inducedEulerPoly}\,\mathbb{Q}\,(\mathrm{inducedCoeff}\,K\,\mu^{-1})\,v$ are the induced Euler polynomials of $\mu$ and of $\mu^{-1}$ at $v$ (finite products of the local induced factors over $w\mid v$), and $\ell=\mathrm{inducedLevelAt}\,K\,\mu\,v=\sum_{w\mid v} f(w/v)\cdot a(\mu_w)$ is the induced level, the sum over $w\mid v$ of the inertia degree times the conductor exponent of $\mu_w$.
--
--   This is the bad-place input to the converse-theorem argument for the cubic induction: it matches the rational functional equation of the trivial-character $\mathrm{GL}_3\times\mathrm{GL}_1$ zeta integrals of the local Whittaker function at a place $v$ which is bad but unramified in $K$ against the expected functional equation of the induced Euler factors, with the local constant computed explicitly as $\prod_{w\mid v}\mu_w(-1)\cdot\prod_{w\mid v}\varepsilon(1/2,\mu_w)$, the first factor being present because $\psi_v$ is the inverse of the standard character. It is used by the two statements producing the corresponding identity uniformly over the cyclic subspace at a deep bad place and over all deep bad places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_eval_mul_eq_finprod_rootNumber_mul_eval_of_forall_localZeta31_fe_one_of_isCubicInductionDataOn_of_addCharLevel.lean

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
  LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal MeasureTheory LanglandsTunnell.RankinSelberg

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in
open scoped Classical in

theorem LanglandsTunnell.CubicInduction.eval_mul_eq_finprod_rootNumber_mul_eval_of_forall_localZeta31_fe_one_of_isCubicInductionDataOn_of_addCharLevel
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
    (hψw : ∀ w ∈ S, LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ w) = 0)
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
          (NumberField.Idele.productMeasureData ℚ S).νS)
    (hKv : ¬ IsRamifiedIn K v) (hψv : LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)

    (hψinv : psiLoc ψ v = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
    M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (harch : (∃ (gInf : GL (Fin 3) (InfiniteAdeleRing ℚ)) (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ), IsAdmissibleTwist ℚ σ ∧
      (∃ (t : ℂ) (e : ℤ), (∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ σ w t e) ∧
        (((1 : (v.adicCompletion ℚ)ˣ →* ℂˣ) (-1) : ℂˣ) : ℂ) = (-1 : ℂ) ^ e) ∧
      ∀ σ₀ : ℝ, ∃ s : ℂ, σ₀ < s.re ∧ archZeta30 ν_mul (fun h => X.whittakerArch (h * gInf)) (σ.comp E) s 1 ≠ 0))
    (R₁ R₂ : Polynomial ℂ) (m : ℤ) (hR₁ : R₁ ≠ 0) (hR₂ : R₂ ≠ 0)
    (hFE1 :
        ∀ g : LocalGL3 v,
          letI := localBorel ℚ v
          ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
            IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (X.whittakerLoc
              v) 1 g σ₀ ∧
            (∀ s : ℂ, σ₀ < s.re →
              localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (X.whittakerLoc v) 1 s g *
                Q₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
              Q₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
            IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt
              ℚ v) (dualWhittakerFn3 (X.whittakerLoc v)) 1⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
            (∀ s : ℂ, σ₁ < (1 - s).re →
              localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
                (X.whittakerLoc v) 1 (1 - s) g *
                (Q₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * R₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) =
              R₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * Q₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) *
                (Ideal.absNorm v.asIdeal : ℂ) ^ (((m : ℂ) + (n : ℂ)) * s))) :
    ∀ s : ℂ,
      R₁.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s) *
          (inducedEulerPoly ℚ (inducedCoeff K μ⁻¹) v).eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))) =
        ((∏ᶠ w ∈ primeFibre ℚ K v, ((localChar μ w (-1) : ℂˣ) : ℂ)) *
            ∏ᶠ w ∈ primeFibre ℚ K v, LanglandsTunnell.TateLocal.stdRootNumberAt K w (localChar μ w)) *
          (Ideal.absNorm v.asIdeal : ℂ) ^ ((inducedLevelAt K μ v : ℂ) * (1 / 2 - s)) *
          (inducedEulerPoly ℚ (inducedCoeff K μ) v).eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) *
          R₂.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by sorry
