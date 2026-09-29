-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_congruenceK1_torusValues_of_isCubicInductionDataOn
-- name    : LanglandsTunnell.CubicInduction.exists_mem_gl3CyclicSubspace_congruenceK1_torusValues_of_isCubicInductionDataOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/7c56b410-03ef-5780-8bf5-d477bcbf3206
-- title:
--   Local newvector of level K₁(ℓᵥ) at twist-ramified primes
-- statement:
--   Let $K$ be a number field with $[K:\mathbb{Q}] = \operatorname{finrank}_{\mathbb{Q}} K = 3$ (hypothesis `hdeg`), equipped with an integral algebra structure of $\mathcal{O}_{\mathbb{Q}}$ on $\mathcal{O}_K$. Let $\psi$ be an additive character of the adele ring of $\mathbb{Q}$ which is a global additive character in the sense of `IsGlobalAddChar`: trivial on the image of $\mathbb{Q}$, continuous and non-trivial. Let $\mu$ be a character of the ideles of $K$ with values in $\mathbb{C}^\times$ which is an admissible twist, i.e. trivial on principal ideles, continuous and unitary.
--
--   The archimedean parameters of $\mu$ are given by data $uR, aR$ at the real places and $uC, kC$ at the complex places, with the hypotheses `huR`, `huC` asserting `IsArchCompAt K μ w` at each place: for a real place $w$ the local component of $\mu$ at $w$ is $x \mapsto \|x\|^{\,\mathrm{mult}(w)\,uR_w}\,(x/\|x\|)^{(aR_w).\mathrm{val}}$, and for a complex place $w$ it is $x \mapsto \|x\|^{\,\mathrm{mult}(w)\,uC_w}\,(x/\|x\|)^{kC_w}$. The hypothesis `hlev` requires that at every finite place $v$ of $\mathbb{Q}$ the local character `psiLoc ψ v` (the restriction of $\psi$ through the embedding of the $v$-component) have level $0$, that is, the supremum of those $n \in \mathbb{Z}$ for which it is trivial on $\{x : v(x) \le \exp n\}$ equals $0$. The hypothesis `hns` states that $\mu$ is not a base-change twist: there is no admissible twist $\eta$ of the ideles of $\mathbb{Q}$ such that for every prime $\mathfrak{P}$ of $\mathcal{O}_K$ at which $\mu$ is unramified and with $\eta$ unramified at the prime below, $\mu(\varpi_{\mathfrak{P}})$ equals $\eta(\varpi_{\mathfrak{P} \cap \mathbb{Q}})$ raised to the inertia degree of $\mathfrak{P}$ over that prime.
--
--   The carrier data consist of a set $D$ of adelic $\mathrm{GL}_2$-matrices, a family $U$ of subgroups indexed by ideals of $\mathcal{O}_{\mathbb{Q}}$ and a family $\mathrm{gen}$ of adelic matrices indexed by the finite places; these assemble into the pins `productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)`, whose measure-theoretic components are the Borel structure and Haar measure on adelic $\mathrm{GL}_2$, the full central subgroup, and the additive adelic Haar measure conditioned on the adelic box. A finite set $S$ of finite places is pinned down by `hS`: a place $w$ lies in $S$ exactly when it is a bad place for $(K,\mu)$, i.e. either ramified in $K$ or carrying a prime of $K$ at which $\mu$ is ramified.
--
--   The datum $X$ is a `CubicInductionData`, consisting of a form $X.\mathrm{form}$ on adelic $\mathrm{GL}_3$ over $\mathbb{Q}$, a global Whittaker function $X.\mathrm{whittaker}$, local Whittaker functions $X.\mathrm{whittakerLoc}\,v$ on $\mathrm{GL}_3$ of the completion at each finite $v$, an archimedean Whittaker function $X.\mathrm{whittakerArch}$, a central character $X.\mathrm{centralChar}$ and a dual Whittaker function $X.\mathrm{dualWhittaker}$. The hypothesis `hX` asserts `IsCubicInductionDataOn K (productionPinsOf …) ψ μ S X`; its clauses (summarised here) require: invariance of the form under left translation by $\mathrm{GL}_3(\mathbb{Q})$ and transformation by $X.\mathrm{centralChar}$ under the adelic centre, with $X.\mathrm{centralChar}$ trivial on principal ideles; cuspidality along the two maximal parabolics $P_{21}$ and $P_{12}$; the identification of $X.\mathrm{whittaker}$ with the $\psi$-Whittaker transform of the form, its $\psi$-Whittaker transformation law under the upper unipotent group, and the mirabolic expansion summing the translates of $X.\mathrm{whittaker}$ to the form; the corresponding local Whittaker laws for each $X.\mathrm{whittakerLoc}\,v$ with respect to `psiLoc ψ v`; factorisation of $X.\mathrm{whittaker}$ at every $g$ as the archimedean value times the product of the local values over any finite set containing $S$ outside which $g$ is integral; sphericality of the induced type, given by the coefficients `inducedCoeff K μ`, at the places outside $S$; right invariance of $X.\mathrm{whittakerLoc}\,v$ under `congruenceK1 (𝓞 ℚ) ℚ v (inducedLevelAt K μ v)` at places outside $S$ that are unramified in $K$; the multiplicity-one property of each local Whittaker function; moderate growth of the form; $K$-finiteness of $X.\mathrm{whittakerArch}$; the iota-moment and Whittaker half-plane conditions; and the dual analogues for $X.\mathrm{dualWhittaker}$ relative to $\psi^{-1}$ and the dual form.
--
--   The analytic hypotheses on this datum are: continuity of the form, of $X.\mathrm{whittaker}$ and of $X.\mathrm{dualWhittaker}$ (`hcont`, `hcontW`, `hcontW'`); gauge majorisation `IsGaugeMajorised3` of $X.\mathrm{whittaker}$ and $X.\mathrm{dualWhittaker}$ (`hW`, `hW'`), i.e. vanishing outside a root-level region and decay in the root gauge there; non-vanishing of $X.\mathrm{whittakerArch}$ (`hne`); and, at each $w \in S$, the four clauses of `hatS`: $X.\mathrm{whittakerLoc}\,w\,1 = 1$; every non-zero element of the cyclic subspace `gl3CyclicSubspace (X.whittakerLoc w)` (the $\mathbb{C}$-span of the right translates) generates $X.\mathrm{whittakerLoc}\,w$ back; $X.\mathrm{whittakerLoc}\,w$ is right invariant under some open subgroup; and for every open subgroup $U_w$ the $U_w$-invariant vectors of that cyclic subspace lie in the span of a finite set. The hypothesis `hcent` requires, at each $w \in S$, that the local component of $X.\mathrm{centralChar}$ at $w$ be unitary and that $X.\mathrm{whittakerLoc}\,w$ transform by it under left multiplication by scalar matrices. The hypothesis `hωcond` requires, at every finite $v$ unramified in $K$, a conductor exponent $a \le \mathrm{inducedLevelAt}\,K\,\mu\,v$ for the local component of $X.\mathrm{centralChar}$ at $v$, in the sense of `HasConductorExponentAt`.
--
--   Further, $E$ is a monoid homomorphism from the units of the infinite adele ring of $\mathbb{Q}$ to the ideles, with `hE` asserting that $E u$ has infinite part $u$ and trivial finite part; $a \in \mathbb{Q}$ is non-zero, $a_\infty$ is a unit of the infinite adele ring whose underlying element is the image of $a$, and $\psi_\infty$ is the additive character $x \mapsto \mathrm{psiArch}(a\,x)$ of the infinite adele ring, with `hψinf` asserting that the restriction of $\psi$ to the archimedean factor is $\psi_\infty$. Measurable and Borel structures on the infinite adele ring and on its unit group are assumed; $\nu_{\mathrm{add}}$ is the measure $|a|^{1/2}$ times the image of Lebesgue measure under the inverse of the identification of the infinite adele ring with the mixed space, and $\nu_{\mathrm{mul}}$ is a Haar measure on the units.
--
--   The hypothesis `hArch` is a conjunction of four groups of conditions on $X.\mathrm{whittakerArch}$. First, continuity together with a uniform bound: there is $t \in \mathbb{N}$ such that for every $N$ there is $C$ with $\|X.\mathrm{whittakerArch}(\mathrm{archComponent3}\,g)\| \le C / \bigl((\prod_w \mathrm{archRoot}_1(w,g)\,\mathrm{archRoot}_2(w,g))^t (1 + \mathrm{archRootSum}(g))^N\bigr)$ for all adelic $g$. Second, the $\psi_\infty$-Whittaker law `IsGL3PsiWhittakerFn psiInf X.whittakerArch`. Third, the central law $X.\mathrm{whittakerArch}(z\cdot g) = X.\mathrm{centralChar}(E z)\,X.\mathrm{whittakerArch}(g)$ for scalar $z$. Fourth, for every admissible twist $\sigma$ of the ideles of $\mathbb{Q}$, every $t \in \mathbb{C}$ and $e \in \mathbb{Z}$ realising the archimedean components of $\sigma$ at the real places of $\mathbb{Q}$, and every $g_\infty \in \mathrm{GL}_3$ of the infinite adele ring, there is a function $P$ differentiable on all of $\mathbb{C}$ with: an abscissa $\sigma_0$ above which the archimedean zeta integral `archZeta30` of $h \mapsto X.\mathrm{whittakerArch}(h\,g_\infty)$ against $\sigma \circ E$ converges, and for $\mathrm{Re}\,s > \sigma_0$ equals $P(s)$ times the archimedean factor of the Hecke datum `heckeDatum K μ (uR + t) (aR + e) (uC + t) kC`; bounds $\|P(s)\| \le C\exp(A|\mathrm{Im}\,s|)$ on every vertical strip; for every strip and every $N$ a bound $|\mathrm{Im}\,s|^N \|P(s)\,\mathrm{archFactor}(s)\| \le C$ for $|\mathrm{Im}\,s| \ge T_0$; and an abscissa $\sigma_1$ above which the dual integral `archZeta31` of `dualWhittakerFn3` against $(\sigma \circ E)^{-1}$ at `weylPrime3 * transposeInv3 1` converges, together with the functional equation, valid for $\sigma_1 < \mathrm{Re}(1-s)$, expressing `archZetaDual31 ν_mul ν_add (fun h => X.whittakerArch (h * gInf)) (σ.comp E) (1 - s) 1` as the product of the root number $\bigl(\prod_{w \text{ real}} \mathrm{signEpsilon}(aR_w + e)\bigr)\bigl(\prod_{w \text{ complex}} i^{|kC_w|}\bigr)\prod_{w} \mathrm{lambdaArch}\,K\,w$ over the places of $K$, the factor $X.\mathrm{centralChar}(E a_\infty)\,\sigma(E a_\infty)^3$, the factor $|a|^{3(s - 1/2)}$, the value $P(s)$, and the dual archimedean factor of the same Hecke datum at $1-s$. Finally, `hArch` requires the existence of an admissible twist $\sigma$ of the ideles of $\mathbb{Q}$ and of some $s$ with `archZeta30 ν_mul X.whittakerArch (σ.comp E) s 1 ≠ 0`.
--
--   Under these hypotheses the conclusion is the following. For every finite place $v$ of $\mathbb{Q}$ such that $\mu$ is ramified at some prime of $K$ above $v$ (`IsTwistRamifiedAbove K μ v`) and such that no prime of $K$ above $v$ has ramification index different from $1$ ($\neg\,$`IsRamifiedIn K v`), there exists a function $W$ in the cyclic subspace `gl3CyclicSubspace (X.whittakerLoc v)`, that is, in the $\mathbb{C}$-span of the right translates of the local Whittaker function at $v$, such that: $W \ne 0$; $W$ is right invariant under `congruenceK1 (𝓞 ℚ) ℚ v (inducedLevelAt K μ v)`, the set of matrices $k$ in the local maximal compact subgroup whose entries $k_{2,0}$, $k_{2,1}$ and $k_{2,2} - 1$ have valuation at most $\exp(-c)$ with $c = \sum_{\mathfrak{P} \mid v} f(\mathfrak{P}/v)\,\mathrm{cond}(\mu_{\mathfrak{P}})$; and, if the level of `psiLoc ψ v` is $0$, then $W(1) = 1$ and $W$ has spherical torus values for the coefficients `inducedCoeff K μ` at $v$, i.e. $W(\mathrm{iotaTorusLocal}\,v\,n) = (\mathrm{cNormQ}\,v)^{-n} S(n)$ for all $n \in \mathbb{N}$ and $W(\mathrm{twoRowPointLocal}\,v\,k_1\,(k_2+1)) = (\mathrm{cNormQ}\,v)^{-k_1}\bigl(S(k_1)S(k_2+1) - S(k_1+1)S(k_2)\bigr)$ whenever $k_2 + 1 \le k_1$, where $S$ denotes `sphericalTorusValue` for the induced elementary symmetric data `inducedE1`, `inducedE2`, `inducedE3` built at $v$ from `inducedCoeff K μ` (which is $\mu(\varpi_{\mathfrak{P}})$ at primes where $\mu$ is unramified and $0$ elsewhere). The hypothesis of this last implication is already granted by `hlev`.
--
--   This is the local step of the cubic induction in the Langlands–Tunnell argument: at a prime $v$ of $\mathbb{Q}$ unramified in the cubic field $K$ but lying below a prime where the twisting character $\mu$ ramifies, the global $\mathrm{GL}_3 \times \mathrm{GL}_1$ analytic package of the induction datum is converted into a non-zero vector of the local Whittaker cyclic space which is invariant under the congruence subgroup $K_1$ of the induced level and whose torus values are those prescribed by the induced Satake coefficients. It feeds the assembly of the full induction datum in [`LanglandsTunnell.CubicInduction.exists_isCubicInductionDataOn_arch_torusValues_localPackage_bad`](thm.html#LanglandsTunnell.CubicInduction.exists_isCubicInductionDataOn_arch_torusValues_localPackage_bad).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_mem_gl3CyclicSubspace_congruenceK1_torusValues_of_isCubicInductionDataOn.lean

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

theorem LanglandsTunnell.CubicInduction.exists_mem_gl3CyclicSubspace_congruenceK1_torusValues_of_isCubicInductionDataOn
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
 :
    ∀ v : HeightOneSpectrum (𝓞 ℚ), IsTwistRamifiedAbove K μ v → ¬ IsRamifiedIn K v →
      ∃ W ∈ gl3CyclicSubspace (X.whittakerLoc v), W ≠ 0 ∧
        (∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ v (inducedLevelAt K μ v), ∀ g, W (g * k) = W g) ∧
        (LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
          W 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v W) := by sorry
