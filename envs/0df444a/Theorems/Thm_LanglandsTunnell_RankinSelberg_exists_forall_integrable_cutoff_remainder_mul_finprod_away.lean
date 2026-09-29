-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_cutoff_remainder_mul_finprod_away
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_integrable_cutoff_remainder_mul_finprod_away
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/c23037cc-ceb2-5590-b064-4e0135caa335
-- title:
--   Cut-off remainder integrands of the dual finite cell are integrable
-- statement:
--   Setting. $K$ is a number field equipped with an integral $\mathcal O_{\mathbb Q}$-algebra structure on $\mathcal O_K$, and the hypothesis `_hdeg` says $[K:\mathbb Q]=3$.
--
--   GL(2) eigensystem data. $\Phi$ is a Hecke eigensystem over $\mathbb Q$ with values in $\mathbb C$, that is, a nonzero level ideal `Φ.level` of $\mathcal O_{\mathbb Q}$ together with families `Φ.a`, `Φ.b` of complex numbers indexed by the height-one primes. $S_Q$ is a finite set of primes of $\mathbb Q$ and `hSQ` has two clauses: every $p$ with `Φ.level` $\le$ $p$ lies in $S_Q$, and every prime $\mathfrak P$ of $K$ whose prime below is outside $S_Q$ has ramification index $1$. Further, `hb` requires $\|\Phi.b\,p\|=1$ for $p\notin S_Q$, and `ha` requires, for every real $\sigma>1$, the summability of $p\mapsto\|\Phi.a\,p\|\,N(p)^{-\sigma}$. A finite set $S_K$ of primes of $K$ is pinned by `hSK` to consist exactly of the primes lying over $S_Q$, and $S$ is a finite set of primes of $\mathbb Q$ with $S\subseteq S_Q$ (`hS`).
--
--   Cusp forms on GL(2). $R$ is a smooth cuspidal realisation at the pins `productionPinsGeneral ℚ` of the renormalised eigensystem `Φ.toRawCentral` (same level and `a`, with $b$ replaced by $N(v)^{-1}\Phi.b\,v$); it carries a function `R.toFun`, a central character `R.centralChar`, and an exceptional set `R.exceptionalSet`, assumed continuous (`hRc`) and with `R.exceptionalSet` $\subseteq S$ (`hRS`). (The name $R$ is reused further on for the family of remainder functions; the realisation occurs only in these earlier hypotheses.) `Cfin` is a function of a finite idele and an adelic $\mathrm{GL}_2$-element, constrained only by `hWfC` below. $\varphi_v$ is a family of functions on $\mathrm{GL}_2(\mathbb A_{\mathbb Q})$ indexed by parity vectors $\mathrm{InfinitePlace}\,\mathbb Q\to\mathbb Z/2$; `hiso` asserts that each $\varphi_v(\mathrm{par})$ is an isotypic cusp form at `productionPinsGeneral ℚ` for the central character `R.centralChar`, level `Φ.level`, exceptional set $S$ and eigensystem $\Phi$ (smooth cuspidality, continuity, right invariance under the level subgroup, Hecke coset eigenfunction with eigenvalue $\Phi.a\,v$ and central eigenvalue `Φ.toRawCentral.b v` outside $S$), `hφne` that each is nonzero, and `hφKf` that each is fixed by right convolution with some factorizable test function.
--
--   Twist and additive character. $\mu$ is a character of the ideles of $K$ and `hμ` is the admissibility of the twist: $\mu$ is an idele class character, continuous and unitary. $\psi$ is an additive character of $\mathbb A_{\mathbb Q}$, `hψ` says it is a global additive character (principal-invariant, continuous, nontrivial), `hlev` that each local component `psiLoc ψ v` has `addCharLevel` equal to $0$, and `hψQ` that $\psi^{-1}$ is the standard character [`NumberField.StandardAddChar.psiQ`](def/NumberField_StandardGlobalAddCharRat.html#L615).
--
--   The cubic induction form. $F$ is a `CubicInductionForm` for $K$, $\psi$, $\mu$ over the pins `productionPinsOf ℚ (classRepSiegelSet ℚ (1/2) 1 (1/2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)`: it packages a function `F.form` on $\mathrm{GL}_3(\mathbb A_{\mathbb Q})$, left invariant under $\mathrm{GL}_3(\mathbb Q)$ and transforming by an idele class central character, cuspidal along both maximal parabolics, together with its $\psi$-Whittaker function `F.whittaker`, local Whittaker functions `F.whittakerLoc v`, archimedean Whittaker function, dual Whittaker function `F.dualWhittaker`, and the accompanying clauses (Whittaker expansion, factorisation into local data away from a finite set containing the bad places, sphericality of the local Whittaker functions at places that are not bad with the Satake data `inducedCoeff K μ`, level invariance at the unramified places, local multiplicity one, moderate growth, $K$-finiteness, and the remaining growth clauses of the structure). The extra hypotheses on $F$ are: `hF0`, saying `F.form` $\neq 0$ and that for every $v$ unramified in $K$ with `addCharLevel (psiLoc ψ v) = 0` one has `F.whittakerLoc v 1 = 1` together with `HasSphericalTorusValuesAt (inducedCoeff K μ) v (F.whittakerLoc v)` (the prescribed values on the one-parameter and two-row torus points in terms of the induced spherical torus values); the continuity hypotheses `hFc`, `hFw`, `hFdw` for `F.form`, `F.whittaker`, `F.dualWhittaker`; the gauge majorisation hypotheses `hFg`, `hFdg` for `F.whittaker` and `F.dualWhittaker` (vanishing off a root-level region and decay $C/(\mathrm{rootSizeProd}^t(1+\mathrm{archRootSum})^N)$ for every $N$); and `hBad`, which for every finite set $T$ of primes provides, at each $v\in T$ that is a bad place for $(K,\mu)$ (ramified in $K$ or twist-ramified above $v$), an open subgroup of $\mathrm{GL}_3(\mathbb Q_v)$ under which `F.whittakerLoc v` is right invariant, and requires that `F.whittakerLoc v` lie in the cyclic subspace generated by any nonzero element of its own cyclic subspace.
--
--   Places, uniformisers and the central translate. $S'$ is a finite set of primes with $S_Q\subseteq S'$ (`hSS'`) such that no prime outside $S'$ is a bad place (`hgood`). $\varpi$ chooses an integer of each completion, with `hπ` saying its image in $\mathbb Q_p$ is nonzero and `hϖ` that its valuation is $\exp(-1)$, for $p\notin S_Q$. The element `hμf` of `finiteAdelicGL2Subgroup ℚ` (the kernel of the archimedean projection) is pinned by `hhμf` to be the product, over the primes of $S'\setminus S_Q$, of the local embeddings of the scalar matrices $\varpi_p$ raised to the power $-\,$`inducedLevelAt K μ p`.
--
--   Whittaker factorisations. $W^A$ and $W^f$ are families, indexed by parity vectors, of functions on $\mathrm{GL}_2(\mathbb R)$ and on `finiteAdelicGL2Subgroup ℚ`; `hWAf` says the $\psi_{\mathbb Q}$-Whittaker coefficient of $\varphi_v(\mathrm{par})$ at $1$ evaluated at $g$ equals $W^A(\mathrm{par})$ at the real archimedean part of $g$ times $W^f(\mathrm{par})$ at the finite factor [`RSCarrier.finFactor g`](def/LanglandsTunnell_RSCarrierSplit.html#L17); `hWfC` identifies $W^f(\mathrm{par})\,g$ with `Cfin 1 g`; `hWf1` says $W^f(\mathrm{par})\,1\neq0$. The element $w_0$ of $\mathrm{GL}_2(\mathbb Q)$ has matrix $\bigl(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\bigr)$ (`hw₀`), and the dual family $W^{f,\vee}$ is defined by `hWfd`: $W^{f,\vee}(\mathrm{par})(g_f)$ is the idele norm of $\det g_f$ times $W^f(\mathrm{par})$ at the finite factor of $w_0\cdot{}^t g_f^{-1}$.
--
--   Measures and parity. Beyond second countability of $\mathrm{GL}_2(\mathbb A_{\mathbb Q})$, $\mu_f$ is a Haar measure on `finiteAdelicGL2Subgroup ℚ`, $\mu_{N,\mathrm{fin}}$ a Haar measure on the finite unipotent subgroup [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43), and a parity vector $\mathrm{par}$ is fixed.
--
--   Pure tensor expansion. $m$ is a natural number, $w$ a family of slot functions $w_{p,\alpha}$ on $\mathrm{GL}_2(\mathbb Q_p)$ for $p\in S_Q$ and $\alpha\in\mathrm{Fin}\,m$, and $W'$ a family of remainders on $\mathrm{GL}_2(\mathbb A_{\mathbb Q})$. The hypotheses are: `_hwlaw`, the local Whittaker law $w_{p,\alpha}(u(x)g)=\psi_{\mathbb Q,p}(x)\,w_{p,\alpha}(g)$; `_hwsm`, right invariance of each slot under an open subgroup; `_hWinv`, right invariance of each $W'_\alpha$ under the place embedding at every $p\in S_Q$; `_hWlaw`, the law $W'_\alpha(u(t)g)=\psi_{\mathbb Q}(t)W'_\alpha(g)$ for adeles $t$ with vanishing archimedean component and trivial unipotent component at all $p\in S_Q$; `_hwmeas` and `_hWmeas`, measurability of the slots and of the remainders on the finite subgroup; `_hsplit`, the expansion $W^f(\mathrm{par})(\mathrm{finFactor}\,g)=\sum_{\alpha}\bigl(\prod_{p\in S_Q}w_{p,\alpha}(g_p)\bigr)W'_\alpha(g)$; and `_hind`, the linear independence over $\mathbb C$ of the $m$ functions $y\mapsto\prod_{p\in S_Q}w_{p,\alpha}(y_p)$. Bumps $W^b_p$ at the primes $p\in S_Q$ are given with `_hWbmem`, $W^b_p\in$ `gl3CyclicSubspace (F.whittakerLoc p)`, and `_hWbone`, $W^b_p(\iota 1)=1$.
--
--   The dual remainders. Finally $R_\alpha$ ($\alpha\in\mathrm{Fin}\,m$) are functions on $\mathrm{GL}_2(\mathbb A_{\mathbb Q})$ with `_hRinv`, right invariance under the place embedding at each $p\in S_Q$, and `_hRexp`, the dual expansion: for every $g$ in the finite subgroup,
--   $$W^{f,\vee}(\mathrm{par})\bigl(\mathrm{finFactor}(g)\cdot h_\mu\bigr)=\sum_{\alpha}\Bigl(\prod_{p\in S_Q}|\det g_p|_p\;w_{p,\alpha}\bigl((w_0)_p\cdot{}^t g_p^{-1}\bigr)\Bigr)R_\alpha(g),$$
--   where $g_p$ denotes the component `localAt ℚ p g`, $h_\mu$ is the element `hμf`, and $|\cdot|_p$ is the local modulus [`LanglandsTunnell.TateLocal.modulus`](def/LanglandsTunnell_TateLocalZeta.html#L15).
--
--   Conclusion. Three assertions hold.
--
--   (i) For each $\alpha$, the function $g\mapsto R_\alpha(g)$ is measurable on `finiteAdelicGL2Subgroup ℚ`.
--
--   (ii) For each $\alpha$, each $n$ in the finite unipotent subgroup [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43) and each $g$ in `finiteAdelicGL2Subgroup ℚ`, one has $\|R_\alpha(ng)\|=\|R_\alpha(g)\|$.
--
--   (iii) There exists a family of subsets $O_p\subseteq\mathrm{GL}_2(\mathbb Q_p)$, indexed by $p\in S_Q$, such that each $O_p$ is open, contains the identity, and satisfies $u(x)y\in O_p\iff y\in O_p$ for all $x\in\mathbb Q_p$ and $y\in\mathrm{GL}_2(\mathbb Q_p)$; and there exists $\sigma\in\mathbb R$ such that for every $\alpha$ and every $s'\in\mathbb C$ with $\sigma<\operatorname{Re}s'$ the function
--   $$g\longmapsto \mathbf 1_{\mathcal C}(g)\Bigl(\prod_{p\in S_Q}\mathbf 1_{O_p}(g_p)\,|\det g_p|_p\Bigr)R_\alpha(g)\;\cdot\;\mathbf 1_{\mathcal C}(g)\ \prod^{\mathrm f}_{v}\Bigl(\mathbf 1_{v\in S_Q}+\mathbf 1_{v\notin S_Q}\,W^\vee_{F,v}\bigl((g\,h_\mu)_v\bigr)\Bigr)\;\cdot\;\|\det g\|_{\mathbb A}^{\,s'-1/2}$$
--   is integrable with respect to `μf.withDensity (HaarQuotient.density RSCarrier.finUnipotent μNFin)`. Here $\mathcal C$ is the set of those $g$ in `finiteAdelicGL2Subgroup ℚ` whose component at every $p\notin S_Q$ factors as $n\,k$ with $n$ in the image of [`AutomorphicForm.unipotentGL2Hom`](def/AutomorphicForm_ConstantTerm.html#L33) over $\mathbb Q_p$ and $k\in$ [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤`](def/AdelicDock_LocalEmbedding.html#L178); the multipliable product is the `finprod` over all primes $v$ of the factor $1$ for $v\in S_Q$ and of `dualWhittakerFn3 (F.whittakerLoc v)`, that is $W\mapsto W(\text{longWeyl}_3\cdot{}^t(\cdot)^{-1})$ applied to `F.whittakerLoc v`, evaluated at the $v$-component of the $\mathrm{GL}_3$-image `iota` of $g\,h_\mu$, for $v\notin S_Q$; and $\|\cdot\|_{\mathbb A}$ is the idele norm [`NumberField.TateGlobal.ideleNorm ℚ`](def/NumberField_TateGlobalZeta.html#L19).
--
--   This is the isolation step in the Rankin–Selberg analysis of the finite cell integral on the Langlands–Tunnell converse-theorem route: after the finite Whittaker function and its dual have been expanded into finitely many pure tensors over the ramified set $S_Q$, it shows that the remainder factors are measurable, have unipotent-invariant absolute value, and that, after cutting off by unipotent-stable open neighbourhoods at the places of $S_Q$ and by the Iwasawa-type cell condition away from $S_Q$, the resulting integrands converge absolutely on a right half-plane. It is used in the proof of the integrability of the pure-tensor terms of the dual and hybrid finite cell integrands, which in turn enters the construction of the global Rankin–Selberg integral attached to the cubic induction form.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_cutoff_remainder_mul_finprod_away.lean

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
import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_LanglandsTunnell_LambdaSquared

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory
open scoped nonZeroDivisors ENNReal
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open LanglandsTunnell.TateLocal UnramifiedWhittaker in
open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.exists_forall_integrable_cutoff_remainder_mul_finprod_away
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ)
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hSQ : (∀ p : HeightOneSpectrum (𝓞 ℚ), Φ.level ≤ p.asIdeal → p ∈ SQ) ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∉ SQ →
        Ideal.ramificationIdx' (𝔓.under (𝓞 ℚ)).asIdeal 𝔓.asIdeal = 1)
    (hb : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ‖Φ.b p‖ = 1)
    (ha : ∀ σ : ℝ, 1 < σ →
      Summable fun p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) =>
        ‖Φ.a p‖ * (Ideal.absNorm p.asIdeal : ℝ) ^ (-σ))
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (hSK : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓 ∈ SK ↔ 𝔓.under (𝓞 ℚ) ∈ SQ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hS : S ⊆ SQ)
    (R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral) (hRc : Continuous R.toFun)
    (Cfin : FiniteAdeleRing (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hRS : R.exceptionalSet ⊆ S)
    (φv : (InfinitePlace ℚ → ZMod 2) → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hiso : ∀ par, IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) R.centralChar Φ.level S Φ (φv par))
    (hφne : ∀ par, φv par ≠ 0)
    (hφKf : ∀ par, ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ (φv par) α = φv par)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)

    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ)
    (hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ)

    (F : CubicInductionForm K (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ψ μ)
    (hF0 : F.form ≠ 0 ∧ ∀ v, ¬ IsRamifiedIn K v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
        F.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v (F.whittakerLoc v))
    (hFc : Continuous F.form) (hFw : Continuous F.whittaker) (hFdw : Continuous F.dualWhittaker)
    (hFg : IsGaugeMajorised3 ℚ F.whittaker) (hFdg : IsGaugeMajorised3 ℚ F.dualWhittaker)
    (hBad :
        ∀ T : Finset (HeightOneSpectrum (𝓞 ℚ)),
          (∀ v ∈ T, IsBadPlace K μ v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
            ∀ k ∈ Uv, ∀ g : LocalGL3 v, F.whittakerLoc v (g * k) = F.whittakerLoc v g) ∧
          (∀ v ∈ T, IsBadPlace K μ v → ∀ W ∈ gl3CyclicSubspace (F.whittakerLoc v), W ≠ 0 →
            F.whittakerLoc v ∈ gl3CyclicSubspace W))

    (S' : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSS' : SQ ⊆ S')
    (hgood : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S' → ¬ IsBadPlace K μ p)
    (ϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p.adicCompletionIntegers ℚ)
    (hπ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p) ≠ 0)
    (hϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) = WithZero.exp (-1 : ℤ))
    (hμf : finiteAdelicGL2Subgroup ℚ)
    (hhμf : (hμf : AdelicGL2 (𝓞 ℚ) ℚ) =
      ((S' \ SQ).toList.map (fun p => if hp : p ∉ SQ then
          UnramifiedWhittaker.placeEmbed ℚ p
            ((UnramifiedWhittaker.scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p))
              (hπ p hp)) ^ (-(inducedLevelAt K μ p : ℤ)))
        else 1)).prod)

    (WA : (InfinitePlace ℚ → ZMod 2) → GL (Fin 2) ℝ → ℂ)
    (Wf : (InfinitePlace ℚ → ZMod 2) → finiteAdelicGL2Subgroup ℚ → ℂ)
    (hWAf : ∀ par (g : AdelicGL2 (𝓞 ℚ) ℚ),
      whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ (φv par) 1 g = WA par (ratArchGL2 g) * Wf par (RSCarrier.finFactor g))
    (hWfC : ∀ par (g : finiteAdelicGL2Subgroup ℚ), Wf par g = Cfin 1 (g : AdelicGL2 (𝓞 ℚ) ℚ))

    (hWf1 : ∀ par, Wf par 1 ≠ 0)

    (w₀ : GL (Fin 2) ℚ) (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) ℚ) = !![0, 1; 1, 0])
    (Wfd : (InfinitePlace ℚ → ZMod 2) → finiteAdelicGL2Subgroup ℚ → ℂ)
    (hWfd : ∀ par (gf : finiteAdelicGL2Subgroup ℚ), Wfd par gf =
      ((NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (gf : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) *
        Wf par (RSCarrier.finFactor (globalPoints (𝓞 ℚ) ℚ w₀ * transposeInvN (Fin 2) (gf : AdelicGL2 (𝓞 ℚ) ℚ))))

    [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)]
    (μf : MeasureTheory.Measure (finiteAdelicGL2Subgroup ℚ)) [μf.IsHaarMeasure]
    (μNFin : MeasureTheory.Measure RSCarrier.finUnipotent) [μNFin.IsHaarMeasure]
    (par : InfinitePlace ℚ → ZMod 2)

    (m : ℕ) (w : ∀ p : ↥SQ, Fin m → GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) → ℂ) (Wrem : Fin m → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (_hwlaw : ∀ (p : ↥SQ) (α : Fin m) (x : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) (g : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)),
      w p α (UnramifiedWhittaker.unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ (p : HeightOneSpectrum (𝓞 ℚ)) x * w p α g)
    (_hwsm : ∀ (p : ↥SQ) (α : Fin m), ∃ U : Subgroup (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ), w p α (g * k) = w p α g)
    (_hWinv : ∀ (α : Fin m) (p : ↥SQ) (x : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      Wrem α (g * UnramifiedWhittaker.placeEmbed ℚ (p : HeightOneSpectrum (𝓞 ℚ)) x) = Wrem α g)
    (_hWlaw : ∀ (α : Fin m) (t : AdeleRing (𝓞 ℚ) ℚ), t.1 = 0 →
      (∀ p : ↥SQ, localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (unipotentGL2 t) = 1) →
      ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, Wrem α (unipotentGL2 t * g) = NumberField.StandardAddChar.psiQ t * Wrem α g)
    (_hwmeas : ∀ (p : ↥SQ) (α : Fin m), Measurable (fun g : finiteAdelicGL2Subgroup ℚ =>
      w p α (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ))))
    (_hWmeas : ∀ α : Fin m, Measurable (fun g : finiteAdelicGL2Subgroup ℚ => Wrem α (g : AdelicGL2 (𝓞 ℚ) ℚ)))
    (_hsplit : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      Wf par (RSCarrier.finFactor g) = ∑ α : Fin m, (∏ p : ↥SQ, w p α (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) g)) * Wrem α g)
    (_hind : LinearIndependent ℂ (fun α : Fin m => fun y : (∀ p : ↥SQ, GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) => ∏ p : ↥SQ, w p α (y p)))

    (Wb : ∀ p : ↥SQ, LocalGL3 p.1 → ℂ)
    (_hWbmem : ∀ p : ↥SQ, Wb p ∈ gl3CyclicSubspace (F.whittakerLoc p.1))
    (_hWbone : ∀ p : ↥SQ, Wb p (iotaGL 1) = 1)

    (R : Fin m → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (_hRinv : ∀ (α : Fin m) (p : ↥SQ) (x : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      R α (g * UnramifiedWhittaker.placeEmbed ℚ (p : HeightOneSpectrum (𝓞 ℚ)) x) = R α g)
    (_hRexp : ∀ g : finiteAdelicGL2Subgroup ℚ, Wfd par (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) * hμf) =
      ∑ α : Fin m, (∏ p : ↥SQ,
        ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ)) :
            ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ) : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) : ℝ) : ℂ) *
          w p α (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (globalPoints (𝓞 ℚ) ℚ w₀) *
            transposeInvN (Fin 2) (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ)))) * R α (g : AdelicGL2 (𝓞 ℚ) ℚ))
    :
    (∀ α : Fin m, Measurable fun g : finiteAdelicGL2Subgroup ℚ => R α (g : AdelicGL2 (𝓞 ℚ) ℚ)) ∧
    (∀ (α : Fin m) (n : ↥RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
      ‖R α (((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)‖ =
        ‖R α (g : AdelicGL2 (𝓞 ℚ) ℚ)‖) ∧
    ∃ O : ∀ p : ↥SQ, Set (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)),
      (∀ p : ↥SQ, IsOpen (O p) ∧ (1 : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) ∈ O p ∧
        ∀ (x : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) (y : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)),
          UnramifiedWhittaker.unipotent x * y ∈ O p ↔ y ∈ O p) ∧
      ∃ σ : ℝ, ∀ (α : Fin m) (s' : ℂ), σ < s'.re →
        Integrable (fun g : finiteAdelicGL2Subgroup ℚ =>
          {g : finiteAdelicGL2Subgroup ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := p.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
                  localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g =>
            (∏ p : ↥SQ, (O p).indicator (fun y =>
              ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det y : ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ) : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) : ℝ) : ℂ))
                (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ))) * R α (g : AdelicGL2 (𝓞 ℚ) ℚ)) g *
          {g : finiteAdelicGL2Subgroup ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := p.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
                  localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => (∏ᶠ v, if v ∈ SQ then (1 : ℂ) else dualWhittakerFn3 (F.whittakerLoc v)
                (componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ ((g * hμf : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ))))) g *
          ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s' - 1 / 2))
        (μf.withDensity (HaarQuotient.density RSCarrier.finUnipotent μNFin)) := by sorry
