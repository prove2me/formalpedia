-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_mem_gl3CyclicSubspace_localZetaDual31_eq_mul_of_cubicInductionForm_twisted_badPlaces_noFE32_adm
-- name    : LanglandsTunnell.CubicInduction.exists_forall_mem_gl3CyclicSubspace_localZetaDual31_eq_mul_of_cubicInductionForm_twisted_badPlaces_noFE32_adm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/0fb25592-f999-509c-8590-01748f2b9fca
-- title:
--   Local constants of twisted cubic induction on the cyclic span
-- statement:
--   Setting. $K$ is a number field of degree $3$ over $\mathbb{Q}$, with $\mathcal{O}_K$ an integral $\mathcal{O}_{\mathbb{Q}}$-algebra; $\Phi$ is a Hecke eigensystem over $\mathbb{Q}$ with complex coefficients, i.e. a non-zero level ideal `Φ.level` of $\mathcal{O}_{\mathbb{Q}}$ together with two families of complex Hecke coefficients indexed by the finite places.
--
--   Place sets. $SQ$ is a finite set of primes of $\mathcal{O}_{\mathbb{Q}}$ and `hSQ` has two clauses: every prime $p$ with `Φ.level` $\subseteq p$ lies in $SQ$, and every prime $\mathfrak{P}$ of $\mathcal{O}_K$ whose restriction to $\mathbb{Q}$ lies outside $SQ$ has ramification index $1$. $SK$ is a finite set of primes of $\mathcal{O}_K$, and `hSK` says $\mathfrak{P}\in SK$ precisely when $\mathfrak{P}$ lies over a prime of $SQ$.
--
--   Characters. $\mu$, $\nu$ are homomorphisms from the idèle units of $K$ to $\mathbb{C}^\times$ and $\chi_{\mathbb{A}}$, $\omega_3$ are such homomorphisms for $\mathbb{Q}$; admissibility (`IsAdmissibleTwist`) of $\mu$, $\nu$, $\chi_{\mathbb{A}}$ means being trivial on principal idèles, continuous and unitary. Further: $\chi_{\mathbb{A}}$ is unramified at every $v\notin SQ$ (`hχoff`) and has trivial archimedean component at each real place of $\mathbb{Q}$, in the sense `IsArchCompAt ℚ χA v 0 0` (`hχinf`); $\mu=\nu\cdot(\chi_{\mathbb{A}}\circ\text{idelic norm of the base change }\mathbb{Q}\to K)$ (`hμν`); and $\nu$ is not of norm type (`hoff`): there is no admissible character $\eta$ of the idèles of $\mathbb{Q}$ with $\nu(\varpi_{\mathfrak{P}})=\eta(\varpi_{p})^{f(\mathfrak{P}|p)}$ for all $\mathfrak{P}$ at which $\nu$ is unramified and $\eta$ is unramified below, $p$ being the prime under $\mathfrak{P}$ and $\varpi$ the uniformiser idèles.
--
--   Depth. `hdepth`: for every $w\in SK$,
--   $$4\bigl(\operatorname{ord}_w(\mathrm{Φ.level}\,\mathcal{O}_K)+\mathrm{addCharLevel}(\psi_{K,w})+1\bigr)\le a_w(\mu_w),$$
--   where $\operatorname{ord}_w$ is the $w$-adic count of the extension of the level to a fractional ideal of $K$, $\psi_{K,w}$ is the standard local additive character, and $a_w$ is `conductorExponentAt`.
--
--   Archimedean parameters of $\nu$. Families $uR,aR$ on the real places and $uC,kC$ on the complex places of $K$ (values in $\mathbb{C}$, $\mathbb{Z}/2$, $\mathbb{C}$, $\mathbb{Z}$) satisfy `IsArchCompAt K ν w (uR w) ((aR w).val)` at real $w$ and `IsArchCompAt K ν w (uC w) (kC w)` at complex $w$ (`hcR`, `hcC`).
--
--   Additive character. $\psi$ is an additive character of the adèles of $\mathbb{Q}$ which is a global additive character (trivial on $\mathbb{Q}$, continuous, non-trivial), all of whose local levels vanish (`hlev`), and with $\psi^{-1}$ equal to the standard character `psiQ` (`hψQ`).
--
--   The cubic determinant character. `hω₃` has three clauses: $\omega_3$ is admissible; at every prime $p$ that is not a bad place for $(K,\nu)$ — i.e. neither ramified in $K$ nor carrying a place of $K$ above it at which $\nu$ is ramified — $\omega_3$ is unramified and its Euler coefficient equals `inducedE3 ℚ (inducedCoeff K ν) p`, minus the degree-$3$ coefficient of the induced Euler polynomial $\prod_{\mathfrak{P}\mid p}(1-c(\mathfrak{P})X^{f(\mathfrak{P}|p)})$ built from the unramified Satake data of $\nu$; and for any archimedean parameters $(uR,aR,uC,kC)$ of $\nu$ as above, $\omega_3$ has archimedean component at each real place of $\mathbb{Q}$ with exponents $\bigl(\sum_{w\text{ real}}uR_w+\sum_{w\text{ complex}}2uC_w,\ \sum_{w\text{ real}}\widetilde{aR_w}+\sum_{w\text{ complex}}(kC_w+1)\bigr)$.
--
--   Archimedean splitting, scaling and measures. $E$ is a monoid homomorphism from the units of the infinite adèles of $\mathbb{Q}$ into the idèle units with `infPart (E u) = u` and trivial finite part (`hE`); $a\in\mathbb{Q}^\times$, $a_\infty$ is a unit of the infinite adèles whose underlying element is the image of $a$, and $\psi_\infty$ is the additive character $x\mapsto\psi_{\mathrm{arch}}(a x)$ (`hpsiInf`), which is the restriction of $\psi$ to the infinite component (`hψinf`). The additive measure $\nu_{\mathrm{add}}$ is $|a|^{1/2}$ times the transport of Lebesgue measure along the identification of the infinite adèles with the mixed space (`hν_add`), and $\nu_{\mathrm{mul}}$ is a Haar measure on the units of the infinite adèles.
--
--   The archimedean Whittaker function. $W_{\mathrm{arch}}$ is a function on $\mathrm{GL}_3$ of the infinite adèles, and `hWarch` consists of seven clauses: $W_{\mathrm{arch}}\neq 0$; $K$-finiteness (the right translates by the orthogonal group `orth3` lie in a fixed finite-dimensional span); continuity together with a gauge bound $\|W_{\mathrm{arch}}(g_\infty)\|\le C/\bigl((\prod_w \mathrm{root}_1\mathrm{root}_2)^t(1+\mathrm{archRootSum})^N\bigr)$ for some $t$ and, for each $N$, some $C$, evaluated along the archimedean component of adelic $g$; the $\psi_\infty$-Whittaker transformation law under upper unipotents; the central law $W_{\mathrm{arch}}(z\cdot g)=\omega_3(E z)W_{\mathrm{arch}}(g)$ for scalar $z$; a zeta-integral clause; and the non-vanishing clause that `archZeta30 ν_mul Warch (σ.comp E) s 1` is non-zero for some admissible $\sigma$ and some $s$. The zeta-integral clause asserts: for every admissible character $\sigma$ of the idèles of $\mathbb{Q}$, every $t\in\mathbb{C}$, $e\in\mathbb{Z}$ with $\sigma$ of archimedean component $(t,e)$ at each real place, and every $g_\infty$, there is an entire $P$ such that (i) for some abscissa $\sigma_0$ the integral `archZeta30` of $h\mapsto W_{\mathrm{arch}}(h g_\infty)$ against $\sigma\circ E$ at the identity converges for $\mathrm{Re}\,s>\sigma_0$ and equals $P(s)$ times the archimedean factor of the $L$-datum `heckeDatum K ν` with parameters $(uR+t,\ aR+e,\ uC+t,\ kC)$; (ii) $P$ is of exponential type on vertical strips; (iii) the product of $P$ with that archimedean factor decays faster than any power of $|\mathrm{Im}\,s|$ on vertical strips; and (iv) for some abscissa $\sigma_1$ the dual integral `archZeta31` of the dual Whittaker function against $(\sigma\circ E)^{-1}$ at `weylPrime3 * transposeInv3 1` converges, and for $\mathrm{Re}(1-s)>\sigma_1$
--   $$\mathrm{archZetaDual31}(1-s)=\Bigl(\prod_{w\text{ real}}\varepsilon(aR_w+e)\cdot\prod_{w\text{ complex}}i^{|kC_w|}\cdot\prod_{w}\lambda_{\mathrm{arch}}(w)\Bigr)\bigl(\omega_3(Ea_\infty)\sigma(Ea_\infty)^3\bigr)|a|^{3(s-1/2)}P(s)\cdot\mathrm{archFactorDual}(1-s),$$
--   the products being over the infinite places of $K$, with `signEpsilon` and `lambdaArch`.
--
--   The cubic induction form. $F$ is a `CubicInductionForm` for $K$, the additive character $\psi$ and the character $\nu$, relative to the carrier pins `productionPinsOf` built from the class-representative centre-cut Siegel set `classRepSiegelSet ℚ (1/2) 1 (1/2) 2`, the level subgroups `levelOne ⊓ finiteAdelicGL2Subgroup`, the Hecke generators `heckeGen`, and the adelic box: thus a cuspidal automorphic function on $\mathrm{GL}_3$ over $\mathbb{Q}$ with its central character, its $\psi$-Whittaker function and Whittaker expansion over the mirabolic index set, local Whittaker functions at the finite places and $F$.`whittakerArch` at infinity, factorisability outside any finite set containing the bad places, induced spherical behaviour with the Satake data `inducedCoeff K ν` at the good places, invariance under `congruenceK1` at the level `inducedLevelAt K ν v` at places unramified in $K$, Whittaker multiplicity one locally, moderate growth, $K$-finiteness and the integrability clauses of that structure. The hypotheses on $F$ are: `hF0`, that $F$.`form` $\neq 0$ and that at every $v$ unramified in $K$ with $\psi_v$ of level $0$ the local Whittaker function is normalised, $W_{F,v}(1)=1$, and has the spherical torus values `HasSphericalTorusValuesAt (inducedCoeff K ν) v`; `hFc`, `hFw`, `hFdw`, continuity of the form, of the Whittaker function and of the dual Whittaker function; `hFg`, `hFdg`, gauge majorisation `IsGaugeMajorised3` of the latter two; `hArchEq`, that $F$.`whittakerArch` $=W_{\mathrm{arch}}$; `hEss`, the existence at each bad place $v$ of $(K,\nu)$ unramified in $K$ with $\psi_v=(\psi_{\mathbb{Q},v})^{-1}$ of an essential vector, namely a non-zero $W$ in the cyclic span `gl3CyclicSubspace` of $W_{F,v}$ under right translation which is a $\psi_v$-Whittaker function, right invariant under `congruenceK1` at the level `inducedLevelAt K ν v`, normalised by $W(1)=1$ and with the spherical torus values for `inducedCoeff K ν`; `hBad`, that for every finite set $T$ of primes and every bad $v\in T$ the function $W_{F,v}$ is right invariant under some open subgroup of $\mathrm{GL}_3(\mathbb{Q}_v)$ and every non-zero member of its cyclic span generates $W_{F,v}$ back; and `hadm`, admissibility: at every bad place $v$ and every open subgroup $U_v$, the $U_v$-right-invariant vectors of the cyclic span of $W_{F,v}$ lie in the span of a finite set of functions.
--
--   Conclusion. There is a function $\lambda$ on the finite places of $\mathbb{Q}$ with values in $\mathbb{C}$ such that the following four assertions hold.
--
--   (1) $\lambda_v=1$ at every $v$ that is not a bad place for $(K,\mu)$.
--
--   (2) $\bigl(\prod_v^{\mathrm{f}}\lambda_v^2\bigr)\cdot$ `lamSqArch K` $=1$, the product being the multiplicative finprod over all finite places, and `lamSqArch K` being $-1$ or $1$ according as the discriminant of $K$ over $\mathbb{Q}$ is negative or not.
--
--   (3) For every $p\in SQ$, every $W$ in the cyclic span of the twisted local Whittaker function $g\mapsto\chi_{\mathbb{A},p}(\det g)\,W_{F,p}(g)$, every $b\in\mathbb{N}$ such that $2\,e(w|p)\,b+1\le a_w(\mu_w)$ for all $w$ in the fibre `primeFibre ℚ K p` over $p$, every character $\eta$ of $(\mathbb{Q}_p)^\times$ admitting a conductor exponent $c_\eta\le b$ in the sense of `HasConductorExponentAt`, every admissible $\eta_{\mathbb{A}}$ over $\mathbb{Q}$ with $p$-component $\eta$ and whose composition with the idelic norm of the base change is admissible over $K$, and every $g\in\mathrm{GL}_3(\mathbb{Q}_p)$: there are polynomials $Q_1,Q_2\in\mathbb{C}[X]$ with $Q_2\neq0$, an integer $n$ and abscissae $\sigma_0,\sigma_1$ such that the integral `localZeta30` for $(W,\eta,g)$ converges for $\mathrm{Re}\,s>\sigma_0$ and there satisfies
--   $$\mathrm{localZeta30}(s)\,Q_2(q_p^{-s})=Q_1(q_p^{-s})\,q_p^{ns},\qquad q_p=\#(\mathcal{O}_{\mathbb{Q}}/p),$$
--   the dual integral `localZeta31` for the dual Whittaker function of $W$, the character $\eta^{-1}$ and the point `weylPrime3 * transposeInv3 g` converges above $\sigma_1$, and for $\sigma_1<\mathrm{Re}(1-s)$
--   $$\mathrm{localZetaDual31}(1-s)\,Q_2(q_p^{-s})=Q_1(q_p^{-s})\,q_p^{ns}\cdot\Bigl(\lambda_p\prod_{w\mid p}^{\mathrm{f}}(\eta_K\mu)_w(-1)\prod_{w\mid p}^{\mathrm{f}}\bigl(\mathrm{stdRootNumberAt}(K,w,(\eta_K\mu)_w)\cdot (q_w^{1/2-s})^{\mathrm{pinnedExp}(K,\eta_K\mu,w)}\bigr)\Bigr),$$
--   where $\eta_K=\eta_{\mathbb{A}}\circ$ (idelic norm of the base change), the products are finprods over the fibre above $p$, $q_w$ is the absolute norm of $w$, and `pinnedExp` is the conductor exponent plus the level of the standard local additive character. The zeta integrals are taken with respect to the multiplicative measure obtained by pulling back along `Units.val` the measure `mulMeasure (selfDualHaarAt ℚ p)`, and the inner additive integrals with respect to `selfDualHaarAt ℚ p`.
--
--   (4) For every finite place $v$ which is a bad place for $(K,\mu)$, lies outside $SQ$, is unramified in $K$ and satisfies $\psi_v=(\psi_{\mathbb{Q},v})^{-1}$, and every $W$ in the cyclic span of $g\mapsto\chi_{\mathbb{A},v}(\det g)W_{F,v}(g)$, and every $g\in\mathrm{GL}_3(\mathbb{Q}_v)$: there are a function $P:\mathbb{C}\to\mathbb{C}$ and abscissae $\sigma_0,\sigma_1$ such that $P$ is a rational function of $q_v^{-s}$ in the sense that $P(s)R(q_v^{-s})=Q(q_v^{-s})q_v^{ms}$ for all $s$, for some $Q,R\in\mathbb{C}[X]$ with $R\neq0$ and some $m\in\mathbb{N}$; the integral `localZeta30` for $W$, the trivial character, and $g$ converges above $\sigma_0$ and equals there
--   $$\bigl(\mathrm{inducedEulerPoly}\,\mathbb{Q}\,(\mathrm{inducedCoeff}\,K\,\mu)\,v\bigr)(q_v^{-s})^{-1}P(s);$$
--   the dual integral `localZeta31` for the dual Whittaker function of $W$, the trivial character, and `weylPrime3 * transposeInv3 g` converges above $\sigma_1$; and for $\sigma_1<\mathrm{Re}(1-s)$
--   $$\mathrm{localZetaDual31}(1-s)=\bigl(\mathrm{inducedEulerPoly}\,\mathbb{Q}\,(\mathrm{inducedCoeff}\,K\,\mu^{-1})\,v\bigr)(q_v^{-(1-s)})^{-1}\Bigl(\lambda_v\cdot\prod_{w\mid v}^{\mathrm{f}}\mu_w(-1)\cdot\prod_{w\mid v}^{\mathrm{f}}\mathrm{stdRootNumberAt}(K,w,\mu_w)\Bigr)q_v^{\,(\mathrm{inducedLevelAt}\,K\,\mu\,v)(1/2-s)}P(s),$$
--   with the same measures as in (3) at the place $v$, the products being finprods over the fibre above $v$, and `inducedLevelAt K μ v` the sum over $w\mid v$ of $f(w|v)\,a_w(\mu_w)$.
--
--   The local hypotheses at the bad places entering this statement are the essential-vector clause `hEss`, the cyclicity and open-invariance clause `hBad` and the admissibility clause `hadm`; no local $\mathrm{GL}_3\times\mathrm{GL}_2$ functional equation is assumed.
--
--   This is the bad-place local-constant identification in the converse-theorem route to automorphic induction from a cubic field: starting from a global cubic induction form twisted by a determinant character, it pins down, uniformly over the whole cyclic span of each local Whittaker function, local functional equations for the $\mathrm{GL}_3\times\mathrm{GL}_1$ zeta integrals, with root numbers and conductors expressed through the Hecke character $\mu$ of $K$ and a place-by-place constant $\lambda$ satisfying a global consistency relation. It is used by the Rankin–Selberg assembly step [`LanglandsTunnell.RankinSelberg.exists_entire_boundedOnStrips_eq_archFactor_mul_lFun_rsDatum_of_le_conductorExponentAt_of_centralInduced_of_localSpaceAt_of_normPin_archTrivial`](thm.html#LanglandsTunnell.RankinSelberg.exists_entire_boundedOnStrips_eq_archFactor_mul_lFun_rsDatum_of_le_conductorExponentAt_of_centralInduced_of_localSpaceAt_of_normPin_archTrivial).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_forall_mem_gl3CyclicSubspace_localZetaDual31_eq_mul_of_cubicInductionForm_twisted_badPlaces_noFE32_adm.lean

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

theorem LanglandsTunnell.CubicInduction.exists_forall_mem_gl3CyclicSubspace_localZetaDual31_eq_mul_of_cubicInductionForm_twisted_badPlaces_noFE32_adm
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ)
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hSQ : (∀ p : HeightOneSpectrum (𝓞 ℚ), Φ.level ≤ p.asIdeal → p ∈ SQ) ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∉ SQ →
        Ideal.ramificationIdx' (𝔓.under (𝓞 ℚ)).asIdeal 𝔓.asIdeal = 1)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (hSK : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓 ∈ SK ↔ 𝔓.under (𝓞 ℚ) ∈ SQ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)

    (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχA : LanglandsTunnell.Converse.IsAdmissibleTwist ℚ χA)
    (hχoff : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → IsUnramifiedCharAt χA v)
    (hχinf : ∀ v : InfinitePlace ℚ, v.IsReal → LanglandsTunnell.Converse.IsArchCompAt ℚ χA v 0 0)
    (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hνadm : LanglandsTunnell.Converse.IsAdmissibleTwist K ν)
    (hμν : μ = ν * χA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
    (hoff : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt ν 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((ν (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
    (hdepth : ∀ w : ↥SK,
      4 * (FractionalIdeal.count K w.1
            ((Φ.level.map (algebraMap (𝓞 ℚ) (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) +
          LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w.1) + 1) ≤
        LanglandsTunnell.TateLocal.conductorExponentAt K w.1 (localChar μ w.1))
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ)
    (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ)
    (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (hcR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K ν w (uR w hw) ((aR w hw).val : ℤ))
    (hcC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K ν w (uC w hw) (kC w hw))
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ)
    (hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ)

    (ω₃ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω₃ : IsAdmissibleTwist ℚ ω₃ ∧
      (∀ p : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K ν p →
        IsUnramifiedCharAt ω₃ p ∧ eulerCoeff ℚ ω₃ p = inducedE3 ℚ (inducedCoeff K ν) p) ∧
      ∀ (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
        (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ),
        (∀ w, ∀ hw : w.IsReal, IsArchCompAt K ν w (uR w hw) ((aR w hw).val : ℤ)) →
        (∀ w, ∀ hw : w.IsComplex, IsArchCompAt K ν w (uC w hw) (kC w hw)) →
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
                  (LanglandsTunnell.HeckeTate.heckeDatum K ν (fun w hw => uR w hw + t)
                    (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactor s) ∧
          (∀ σ₁ σ₂ : ℝ, ∃ C A : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
            ‖P s‖ ≤ C * Real.exp (A * |s.im|)) ∧
          (∀ (σ₁ σ₂ : ℝ) (N : ℕ), ∃ C T₀ : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → T₀ ≤ |s.im| →
            |s.im| ^ N *
              ‖P s *
                (LanglandsTunnell.HeckeTate.heckeDatum K ν (fun w hw => uR w hw + t)
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
                  (LanglandsTunnell.HeckeTate.heckeDatum K ν (fun w hw => uR w hw + t)
                    (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactorDual (1 - s))) ∧
      ∃ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ ∧
        ∃ s : ℂ, archZeta30 ν_mul Warch (σ.comp E) s 1 ≠ 0)

    (F : CubicInductionForm K (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ψ ν)
    (hF0 : F.form ≠ 0 ∧ ∀ v, ¬ IsRamifiedIn K v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
        F.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K ν) v (F.whittakerLoc v))
    (hFc : Continuous F.form) (hFw : Continuous F.whittaker) (hFdw : Continuous F.dualWhittaker)
    (hFg : IsGaugeMajorised3 ℚ F.whittaker) (hFdg : IsGaugeMajorised3 ℚ F.dualWhittaker)
    (hArchEq : F.whittakerArch = Warch)
    (hEss :
      (∀ v : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K ν v → ¬ IsRamifiedIn K v →
        psiLoc ψ v = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ →
        ∃ W ∈ gl3CyclicSubspace (F.whittakerLoc v), IsGL3PsiWhittakerFn (psiLoc ψ v) W ∧ W ≠ 0 ∧
          (∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ v (inducedLevelAt K ν v), ∀ g, W (g * k) = W g) ∧
          W 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K ν) v W))
    (hBad :
        ∀ T : Finset (HeightOneSpectrum (𝓞 ℚ)),
          (∀ v ∈ T, IsBadPlace K ν v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
            ∀ k ∈ Uv, ∀ g : LocalGL3 v, F.whittakerLoc v (g * k) = F.whittakerLoc v g) ∧
          (∀ v ∈ T, IsBadPlace K ν v → ∀ W ∈ gl3CyclicSubspace (F.whittakerLoc v), W ≠ 0 →
            F.whittakerLoc v ∈ gl3CyclicSubspace W))

    (hadm : ∀ v : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K ν v →
      ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
        ∃ B : Finset (LocalGL3 v → ℂ), ∀ G ∈ gl3CyclicSubspace (F.whittakerLoc v),
          (∀ k ∈ Uv, ∀ g : LocalGL3 v, G (g * k) = G g) → G ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ))) :
    ∃ lamM : HeightOneSpectrum (𝓞 ℚ) → ℂ,
      (∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ v → lamM v = 1) ∧
      (∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), lamM v ^ 2) * lamSqArch K = 1 ∧
      (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ SQ → ∀ W ∈ gl3CyclicSubspace
          (fun g : LocalGL3 p => ((NumberField.TateGlobal.localChar χA p (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            F.whittakerLoc p g),
    ∀ b : ℕ,
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
                    (lamM p *
                      (∏ᶠ w ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ K p,
                        ((NumberField.TateGlobal.localChar
                          (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w (-1) : ℂˣ) : ℂ)) *
                      (∏ᶠ w ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ K p,
                        (LanglandsTunnell.TateLocal.stdRootNumberAt K w
                            (NumberField.TateGlobal.localChar
                              (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w) *
                          (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^
                            (LanglandsTunnell.Converse.pinnedExp K
                                (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w)))))) ∧

      (∀ v : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ v → v ∉ SQ → ¬ IsRamifiedIn K v →
        psiLoc ψ v = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ →
        ∀ W ∈ gl3CyclicSubspace
          (fun g : LocalGL3 v => ((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            F.whittakerLoc v g),
        (∀ g : LocalGL3 v,
          (letI := localBorel ℚ v
           ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
            (∃ (Q R : Polynomial ℂ) (m : ℕ), R ≠ 0 ∧ ∀ s : ℂ,
              P s * R.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
                Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
            IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 g σ₀ ∧
            (∀ s : ℂ, σ₀ < s.re →
              localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) W 1 s g =
                ((inducedEulerPoly ℚ (inducedCoeff K μ) v).eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹ * P s) ∧
            IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
              (selfDualHaarAt ℚ v) (dualWhittakerFn3 W) 1 (weylPrime3 * transposeInv3 g) σ₁ ∧
            ∀ s : ℂ, σ₁ < (1 - s).re →
              localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
                  W 1 (1 - s) g =
                ((inducedEulerPoly ℚ (inducedCoeff K μ⁻¹) v).eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))))⁻¹ *
                  (((lamM v *
                      ((∏ᶠ w ∈ primeFibre ℚ K v, ((localChar μ w (-1) : ℂˣ) : ℂ)) *
                        ∏ᶠ w ∈ primeFibre ℚ K v, LanglandsTunnell.TateLocal.stdRootNumberAt K w (localChar μ w))) *
                      (Ideal.absNorm v.asIdeal : ℂ) ^ ((inducedLevelAt K μ v : ℂ) * (1 / 2 - s))) * P s)))) := by sorry
