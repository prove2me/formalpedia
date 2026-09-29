-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_mem_gl3CyclicSubspace_localZetaDual31_eq_mul_of_isCubicInductionDataOn_deep_badPlaces
-- name    : LanglandsTunnell.CubicInduction.exists_forall_mem_gl3CyclicSubspace_localZetaDual31_eq_mul_of_isCubicInductionDataOn_deep_badPlaces
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/636987b7-914b-518c-88a5-3a36b8ee5792
-- title:
--   Span-wide local constants for deep cubic induction data
-- statement:
--   Setting. Let $K$ be a number field with $[K:\mathbb Q]=\operatorname{finrank}_{\mathbb Q}K=3$, equipped with an algebra structure $\mathcal O_{\mathbb Q}\to\mathcal O_K$ making $\mathcal O_K$ integral over $\mathcal O_{\mathbb Q}$. Let $SQ$ be a finite set of height-one primes of $\mathcal O_{\mathbb Q}$ such that every prime $\mathfrak P$ of $\mathcal O_K$ whose contraction $\mathfrak P\cap\mathcal O_{\mathbb Q}$ lies outside $SQ$ has ramification index $e(\mathfrak P/\mathfrak p)=1$ (hypothesis `hSQ`: $SQ$ contains all primes ramified in $K$). Let $\mu\colon (\mathbb A_K)^\times\to\mathbb C^\times$ be an admissible twist of $K$, i.e. trivial on principal ideles, continuous, and unitary (`hμ`). The hypothesis `hoff` asserts that $\mu$ is not of norm type: there is no admissible twist $\eta$ of $\mathbb Q$ with $\mu(\varpi_{\mathfrak P})=\eta(\varpi_{\mathfrak p})^{f(\mathfrak P/\mathfrak p)}$ for all $\mathfrak P$ at which $\mu$ is unramified and lying over a prime $\mathfrak p$ at which $\eta$ is unramified, $\varpi$ denoting the uniformizer ideles and $f$ the inertia degree. The hypothesis `hdeep` asserts that $\mu$ is ramified above $SQ$: the conductor exponent of the local component of $\mu$ at $\mathfrak P$ is $\ge 1$ whenever $\mathfrak P$ lies over a prime of $SQ$.
--
--   Archimedean parameters and additive character. Functions $uR,aR$ on the real places and $uC,kC$ on the complex places of $K$ (values in $\mathbb C$, $\mathbb Z/2$, $\mathbb C$, $\mathbb Z$ respectively) are given, with `hcR`, `hcC` asserting `IsArchCompAt` at every archimedean place: the local component of $\mu$ at $w$ is $x\mapsto \lVert x\rVert^{\mathrm{mult}(w)\,u}\,(x/\lVert x\rVert)^{a}$ with $(u,a)=(uR_w,(aR_w).\mathrm{val})$ at real $w$ and $(u,a)=(uC_w,kC_w)$ at complex $w$. Further, $\psi$ is a global additive character of $\mathbb A_{\mathbb Q}$ (trivial on $\mathbb Q$, continuous, non-trivial), all of whose local components have additive level $0$ (`hlev`), and $\psi^{-1}$ is the standard character `psiQ` (`hψQ`).
--
--   The induced central character. A character $\omega_3$ of the ideles of $\mathbb Q$ is given, with `hω₃` asserting three things: $\omega_3$ is an admissible twist of $\mathbb Q$; at every prime $p$ which is not a bad place of $(K,\mu)$ — bad meaning ramified in $K$ or carrying a prime of $K$ at which $\mu$ is ramified — $\omega_3$ is unramified and its Euler coefficient equals $\mathrm{inducedE}_3$ of the induced coefficients of $\mu$ at $p$, i.e. minus the degree-$3$ coefficient of $\prod_{\mathfrak P\mid p}(1-\mathrm{inducedCoeff}(\mu)(\mathfrak P)X^{f(\mathfrak P/p)})$; and, for any archimedean data $(uR,aR,uC,kC)$ satisfying the two `IsArchCompAt` conditions for $\mu$, at every real place $v$ of $\mathbb Q$ the character $\omega_3$ has archimedean components $\bigl(\sum_{w\ \mathrm{real}}uR_w+\sum_{w\ \mathrm{cplx}}2uC_w,\ \sum_{w\ \mathrm{real}}(aR_w).\mathrm{val}+\sum_{w\ \mathrm{cplx}}(kC_w+1)\bigr)$.
--
--   Splitting and archimedean normalisations. $E$ is a homomorphism from the units of the infinite adeles to the ideles of $\mathbb Q$ splitting off the infinite part: $\mathrm{infPart}(E u)=u$ and $\mathrm{finPart}(E u)=1$ (`hE`). A non-zero $a\in\mathbb Q$ is given together with a unit $a_\infty$ of the infinite adeles equal to the image of $a$, and an additive character $\psi_\infty$ of the infinite adeles with $\psi_\infty(x)=\mathrm{psiArch}(a x)$; $\psi$ restricted along the inclusion of the infinite component equals $\psi_\infty$ (`hψinf`). The measure $\nu_{\mathrm{add}}$ is $|a|^{1/2}$ times the Lebesgue measure of the mixed space transported to the infinite adeles, and $\nu_{\mathrm{mul}}$ is a Haar measure on the units of the infinite adeles; the relevant Borel measurable structures are fixed.
--
--   The archimedean Whittaker function. A function $W_\infty=$ `Warch` on $GL_3$ of the infinite adeles is given, and the hypothesis `hWarch` (a conjunction of six groups of clauses, summarised here) asserts: $W_\infty\neq0$; $W_\infty$ is $K$-finite (its right translates by the orthogonal group lie in a fixed finite-dimensional span); $W_\infty$ is continuous and there is $t$ such that for every $N$ some $C$ bounds $\lVert W_\infty(\text{archimedean component of }g)\rVert$ by $C$ divided by $(\prod_w \mathrm{archRoot}_1\mathrm{archRoot}_2)^t(1+\mathrm{archRootSum})^N$; $W_\infty$ satisfies the $\psi_\infty$-Whittaker law $W_\infty(u(x,y,z)g)=\psi_\infty(x+y)W_\infty(g)$ for upper unipotent $u(x,y,z)$; $W_\infty(\mathrm{scalar}(z)g)=\omega_3(E z)W_\infty(g)$; and the archimedean zeta package: for every admissible twist $\sigma$ of $\mathbb Q$, every $t\in\mathbb C$, $e\in\mathbb Z$ which are the archimedean components of $\sigma$ at every real place of $\mathbb Q$, and every $g_\infty$, there is an entire $P$ such that (i) for some $\sigma_0$ the $\mathrm{archZeta}_{3,0}$ integral of $h\mapsto W_\infty(hg_\infty)$ against $\sigma\circ E$ converges for $\mathrm{Re}\,s>\sigma_0$ and equals $P(s)$ times the archimedean factor of the Hecke datum $\mathrm{heckeDatum}\,K\,\mu\,(uR+t)\,(aR+e)\,(uC+t)\,kC$; (ii) $P$ is of bounded exponential type $C e^{A|\mathrm{Im}\,s|}$ in every vertical strip; (iii) in every vertical strip and for every $N$, $|\mathrm{Im}\,s|^N$ times the norm of $P(s)$ times that archimedean factor is bounded for $|\mathrm{Im}\,s|$ large; (iv) for some $\sigma_1$ the dual integral $\mathrm{archZeta}_{3,1}$ for $\mathrm{dualWhittakerFn}_3$ converges, and for $\sigma_1<\mathrm{Re}(1-s)$ the functional equation
--   $$\mathrm{archZetaDual}_{3,1}(1-s)=\Bigl(\prod_{w\ \mathrm{real}}\mathrm{signEpsilon}(aR_w+e)\cdot\prod_{w\ \mathrm{cplx}}i^{|kC_w|}\cdot\prod_{w}\lambda_{\mathrm{arch}}(K,w)\Bigr)\bigl(\omega_3(Ea_\infty)\sigma(Ea_\infty)^3\bigr)|a|^{3(s-1/2)}P(s)\,\mathrm{archFactorDual}(1-s)$$
--   of the same Hecke datum; finally, there is an admissible twist $\sigma$ of $\mathbb Q$ and an $s$ with $\mathrm{archZeta}_{3,0}(\nu_{\mathrm{mul}},W_\infty,\sigma\circ E,s,1)\neq0$.
--
--   The cubic induction data. A set $D$, a family $U$ of subgroups indexed by ideals, and Hecke generators $\mathrm{gen}$ for $GL_2$ of the adeles of $\mathbb Q$ are given, together with $X\colon$ `CubicInductionData`, consisting of a form, a Whittaker function and its dual, local Whittaker functions at each prime, an archimedean Whittaker function and a central character. The hypothesis `hX` asserts `IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ μ S X` with $S=\{v: v\text{ bad for }(K,\mu)\}$; its clauses (summarised here) require: left $GL_3(\mathbb Q)$-invariance of `X.form`, the central law with central character `X.centralChar`, that this character be an idele class character, cuspidality along the radicals of the $(2,1)$- and $(1,2)$-parabolics, that `X.whittaker` be the $\psi$-Whittaker integral of `X.form` and satisfy the $\psi$-Whittaker law, the mirabolic Fourier expansion recovering `X.form`, the local $\psi_v$-Whittaker laws, factorisation of `X.whittaker` over any finite set of primes containing $S$ into `X.whittakerArch` at the archimedean component times the local factors, induced sphericity of the local factors off $S$, level invariance under the congruence subgroups $K_1$ of level $\mathrm{inducedLevelAt}(K,\mu)$ off $S$ at primes unramified in $K$, local multiplicity one, moderate growth of the form, $K$-finiteness of the archimedean factor, the iota-moment and Whittaker half-plane integrability conditions, and the corresponding statements for $\psi^{-1}$ and the dual form. In addition: `hX0` asserts `X.form` $\neq0$ and, at every good $v$ where $\psi_v$ has level $0$, $W_{X,v}(1)=1$ together with the spherical torus values of the induced coefficients of $\mu$; `hX1` asserts $W_{X,w}(1)=1$ at every bad $w$; `hXc`, `hXw`, `hXdw` assert continuity of the form, the Whittaker function and the dual Whittaker function; `hXg`, `hXdg` assert that these last two are gauge-majorised (supported in a root level and bounded by $C/(\mathrm{rootSizeProd}^t(1+\mathrm{archRootSum})^N)$ there); `hArchEq` asserts `X.whittakerArch` $=W_\infty$; `hBad` asserts, for every finite set $T$ of primes, that at each bad $v\in T$ the local factor $W_{X,v}$ is right invariant under some open subgroup and that every non-zero element of the cyclic span $\mathrm{gl3CyclicSubspace}(W_{X,v})$ (the span of the right translates) generates $W_{X,v}$ in its own cyclic span; `hadm` asserts admissibility: at each bad $w$ and each open subgroup $U_w$ there is a finite set $B$ of functions spanning all $U_w$-right-invariant members of the cyclic span of $W_{X,w}$; and `hcent` asserts, at each bad $w$, that the local component of `X.centralChar` is unitary and that $W_{X,w}(\mathrm{scalar}(t)h)=\mathrm{localChar}(\mathrm{X.centralChar})_w(t)\,W_{X,w}(h)$.
--
--   Conclusion. There exists a function $\lambda\colon\{\text{primes of }\mathcal O_{\mathbb Q}\}\to\mathbb C$ with the following four properties.
--
--   (1) $\lambda(v)=1$ at every prime $v$ that is not bad for $(K,\mu)$.
--
--   (2) $\bigl(\prod^{\mathrm f}_{v}\lambda(v)^2\bigr)\cdot\mathrm{lamSqArch}(K)=1$, where $\mathrm{lamSqArch}(K)$ is $-1$ if the discriminant $\mathrm{discr}_{\mathbb Q}(K)$ is negative and $1$ otherwise, and the product is the finitely-supported product over all primes.
--
--   (3) For every $p\in SQ$, every $W$ in the cyclic span $\mathrm{gl3CyclicSubspace}(W_{X,p})$, every $b\in\mathbb N$ such that $2e(w/p)b+1\le$ (conductor exponent of the local component of $\mu$ at $w$) for every $w$ in the fibre of $p$ in $K$, every character $\eta$ of the units of the completion at $p$ having conductor exponent $c_\eta\le b$, every admissible twist $\eta_A$ of $\mathbb Q$ whose local component at $p$ is $\eta$ and whose composite $\chi:=\eta_A\circ N$ with the idelic norm of the genuine base change $\mathbb Q\to K$ is an admissible twist of $K$, and every $g\in GL_3$ of the completion at $p$: there are polynomials $Q_1,Q_2\in\mathbb C[X]$ with $Q_2\neq0$, an integer $n$ and reals $\sigma_0,\sigma_1$ such that, with respect to the multiplicative measure obtained from the self-dual additive Haar measure at $p$ by comap along $\mathrm{Units.val}$, the zeta integral $Z_{3,0}$ of $W$ against $\eta$ at $g$ converges for $\mathrm{Re}\,s>\sigma_0$ and satisfies there
--   $$Z_{3,0}(s)\,Q_2(Np^{-s})=Q_1(Np^{-s})\,Np^{\,n s},$$
--   the dual integral $Z_{3,1}$ for $\mathrm{dualWhittakerFn}_3(W)$, $\eta^{-1}$ at $w'\,{}^t g^{-1}$ (with $w'=\mathrm{weylPrime}_3$) converges for $\mathrm{Re}\,s>\sigma_1$, and for $\sigma_1<\mathrm{Re}(1-s)$
--   $$Z^{\vee}_{3,1}(1-s)\,Q_2(Np^{-s})=Q_1(Np^{-s})\,Np^{\,n s}\cdot\Bigl(\lambda(p)\ \prod^{\mathrm f}_{w\mid p}\chi_w(-1)\ \prod^{\mathrm f}_{w\mid p}\bigl(\mathrm{stdRootNumberAt}(K,w,\chi_w)\,(Nw^{1/2-s})^{\mathrm{pinnedExp}(K,\chi,w)}\bigr)\Bigr),$$
--   where $\chi_w$ denotes the local component of $\chi\cdot\mu$ at $w$ (more precisely of $(\eta_A\circ N)\cdot\mu$), the products run over the fibre of $p$ in $K$, and $\mathrm{pinnedExp}$ is the conductor exponent plus the level of the standard local character.
--
--   (4) For every bad prime $v\notin SQ$ that is unramified in $K$ and satisfies $\psi_v=(\mathrm{psiLocal}_{\mathbb Q,v})^{-1}$, every $W$ in the cyclic span of $W_{X,v}$ and every $g\in GL_3$ of the completion at $v$: there are a function $P\colon\mathbb C\to\mathbb C$ and reals $\sigma_0,\sigma_1$ such that $P$ is rational in $Nv^{-s}$ up to a power, i.e. there are polynomials $Q,R$ with $R\neq0$ and $m\in\mathbb N$ with $P(s)R(Nv^{-s})=Q(Nv^{-s})Nv^{\,m s}$ for all $s$; the zeta integral $Z_{3,0}$ of $W$ against the trivial character at $g$ converges for $\mathrm{Re}\,s>\sigma_0$ and equals there
--   $$Z_{3,0}(s)=\bigl(\mathrm{inducedEulerPoly}_{\mathbb Q}(\mathrm{inducedCoeff}(K,\mu),v)(Nv^{-s})\bigr)^{-1}P(s);$$
--   the dual integral converges for $\mathrm{Re}\,s>\sigma_1$, and for $\sigma_1<\mathrm{Re}(1-s)$
--   $$Z^{\vee}_{3,1}(1-s)=\bigl(\mathrm{inducedEulerPoly}_{\mathbb Q}(\mathrm{inducedCoeff}(K,\mu^{-1}),v)(Nv^{-(1-s)})\bigr)^{-1}\cdot\Bigl(\lambda(v)\bigl(\textstyle\prod^{\mathrm f}_{w\mid v}\mu_w(-1)\bigr)\bigl(\prod^{\mathrm f}_{w\mid v}\mathrm{stdRootNumberAt}(K,w,\mu_w)\bigr)\Bigr)\,Nv^{\,\mathrm{inducedLevelAt}(K,\mu,v)(1/2-s)}\,P(s),$$
--   where $\mu_w$ is the local component of $\mu$ at $w$ and $\mathrm{inducedLevelAt}(K,\mu,v)=\sum_{w\mid v}f(w/v)\cdot(\text{conductor exponent of }\mu_w)$.
--
--   Thus a single constant $\lambda(p)$ per prime, independent of the vector $W$ in the cyclic span, of the depth parameter $b$, of the twist $\eta$ and its global realisation $\eta_A$, and of $g$, governs the local $GL_3\times GL_1$ functional equations, and these constants satisfy the global product relation (2).
--
--   This is the span-wide identification of the local $GL_3\times GL_1$ constants of a cubic induction datum: at the deep primes of $SQ$ and at the remaining bad primes, the local zeta integrals of any vector in the cyclic span of the local Whittaker factor satisfy a functional equation with root number given by the product of the standard local root numbers of the twisted character over the fibre, up to one constant $\lambda(p)$ per prime, the $\lambda(p)^2$ multiplying the archimedean sign to $1$. It feeds the converse-theorem input for the automorphic induction of an idele class character of a cubic field, and is used by [`LanglandsTunnell.CubicInduction.exists_forall_mem_gl3CyclicSubspace_localZetaDual31_eq_mul_of_cubicInductionForm_twisted_badPlaces_noFE32_adm`](thm.html#LanglandsTunnell.CubicInduction.exists_forall_mem_gl3CyclicSubspace_localZetaDual31_eq_mul_of_cubicInductionForm_twisted_badPlaces_noFE32_adm).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_forall_mem_gl3CyclicSubspace_localZetaDual31_eq_mul_of_isCubicInductionDataOn_deep_badPlaces.lean

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

theorem LanglandsTunnell.CubicInduction.exists_forall_mem_gl3CyclicSubspace_localZetaDual31_eq_mul_of_isCubicInductionDataOn_deep_badPlaces
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)

    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hSQ : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∉ SQ →
      Ideal.ramificationIdx' (𝔓.under (𝓞 ℚ)).asIdeal 𝔓.asIdeal = 1)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (hoff : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
    (hdeep : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∈ SQ →
      1 ≤ LanglandsTunnell.TateLocal.conductorExponentAt K 𝔓 (localChar μ 𝔓))
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
    ∃ lamM : HeightOneSpectrum (𝓞 ℚ) → ℂ,
      (∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ v → lamM v = 1) ∧
      (∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), lamM v ^ 2) * lamSqArch K = 1 ∧
      (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ SQ → ∀ W ∈ gl3CyclicSubspace (X.whittakerLoc p), ∀ b : ℕ,
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
        ∀ W ∈ gl3CyclicSubspace (X.whittakerLoc v),
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
