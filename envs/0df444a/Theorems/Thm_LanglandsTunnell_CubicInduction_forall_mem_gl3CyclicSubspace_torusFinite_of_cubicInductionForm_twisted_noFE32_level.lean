-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_torusFinite_of_cubicInductionForm_twisted_noFE32_level
-- name    : LanglandsTunnell.CubicInduction.forall_mem_gl3CyclicSubspace_torusFinite_of_cubicInductionForm_twisted_noFE32_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/f0ed0d08-37c3-5089-bc1b-cada169e4899
-- title:
--   Finiteness of torus coefficients in the twisted local cyclic space
-- statement:
--   Throughout, $K$ is a number field equipped with an $\mathcal O_{\mathbb Q}$-algebra structure on $\mathcal O_K$ which is integral. **Eigensystem and places.** $\Phi$ is a Hecke eigensystem over $\mathbb Q$ with values in $\mathbb C$, so a datum consisting of a non-zero ideal $\Phi.\mathrm{level}$ of $\mathcal O_{\mathbb Q}$ together with families $a,b$ of complex Hecke parameters. $SQ$ is a finite set of finite places of $\mathbb Q$ and `hSQ` has two clauses: every $p$ with $\Phi.\mathrm{level}\subseteq p$ lies in $SQ$, and every prime $\mathfrak P$ of $\mathcal O_K$ whose trace to $\mathcal O_{\mathbb Q}$ is outside $SQ$ has ramification index $1$. $SK$ is a finite set of primes of $K$, and `hSK` says $\mathfrak P\in SK$ if and only if $\mathfrak P$ lies over a prime in $SQ$. **Characters.** $\mu$ is an idèle character of $K$ which is admissible in the sense of `IsAdmissibleTwist` (trivial on principal idèles, continuous, unitary). $\chi_A$ is an admissible idèle character of $\mathbb Q$ which, by `hχoff`, is unramified at every $v\notin SQ$; $k_\chi$ assigns to each finite place a natural number, and `hkχ` says that for $p\in SQ$ the local component of $\chi_A$ at $p$ has conductor exponent $k_\chi(p)$ (trivial on the $k_\chi(p)$-th higher unit group and non-trivial on each smaller one). By `hχinf`, at every real place of $\mathbb Q$ the archimedean component of $\chi_A$ has parameters $(0,0)$. $\nu$ is a further admissible idèle character of $K$, and `hμν` factors $\mu=\nu\cdot(\chi_A\circ N)$, where $N$ is the idèlic norm attached to the base change $\mathbb Q\to K$. The hypothesis `hoff` asserts that $\nu$ is not of norm type: there is no admissible idèle character $\eta$ of $\mathbb Q$ such that, whenever $\nu$ is unramified at $\mathfrak P$ and $\eta$ is unramified at the prime $p$ below it, $\nu$ of a uniformiser idèle at $\mathfrak P$ equals $\eta$ of a uniformiser idèle at $p$ raised to the residue degree $f(\mathfrak P/p)$. The depth hypothesis `hdepth` requires, for every $w\in SK$, that
--   $$4\bigl(\operatorname{ord}_w(\Phi.\mathrm{level}\,\mathcal O_K)+\mathrm{addCharLevel}(\psi^{\mathrm{loc}}_{K,w})+1\bigr)\le \mathrm{conductorExponentAt}_w(\mu_w).$$ The archimedean data $u_R,a_R$ (at real places of $K$, with $a_R$ valued in $\mathbb Z/2$) and $u_C,k_C$ (at complex places) satisfy `hcR`, `hcC`: $\nu$ has archimedean component $(u_R(w),a_R(w))$ at each real $w$ and $(u_C(w),k_C(w))$ at each complex $w$, in the sense of `IsArchCompAt`. **Additive character and the auxiliary character $\omega_3$.** $\psi$ is an additive character of the adèles of $\mathbb Q$ which is a global additive character (trivial on $\mathbb Q$, continuous, non-trivial); `hlev` says every local component $\mathrm{psiLoc}\,\psi\,v$ has level $0$, and `hψQ` identifies $\psi^{-1}$ with the standard character `psiQ`. The character $\omega_3$ of the idèles of $\mathbb Q$ satisfies `hω₃`, three clauses: it is admissible; at every place $p$ which is not bad for $(K,\nu)$ (bad meaning ramified in $K$ or carrying a prime above it at which $\nu$ is ramified) it is unramified with Euler coefficient equal to $\mathrm{inducedE3}$ of the induced Euler polynomial of the coefficients $\mathrm{inducedCoeff}(K,\nu)$ at $p$; and for any archimedean data for $\nu$ as above, at every real place of $\mathbb Q$ the archimedean component of $\omega_3$ has parameters $\bigl(\sum_{w\ \mathrm{real}}u_R(w)+\sum_{w\ \mathrm{complex}}2u_C(w),\ \sum_{w\ \mathrm{real}}a_R(w)+\sum_{w\ \mathrm{complex}}(k_C(w)+1)\bigr)$, the sums being finsums over the infinite places of $K$. **Archimedean splitting, scaling and measures.** $E$ is a monoid homomorphism from the units of the infinite adèles of $\mathbb Q$ to the idèles with `hE`: the infinite part of $E(u)$ is $u$ and its finite part is $1$. A non-zero rational $a$ is fixed, $a_\infty$ is the unit of the infinite adèles with underlying value the image of $a$, and $\psi_\infty$ is the additive character $x\mapsto \mathrm{psiArch}(a\,x)$ on the infinite adèles; `hψinf` says that the restriction of $\psi$ along the inclusion of the infinite component equals $\psi_\infty$. Borel measurable structures on the infinite adèles and on their unit group are fixed; $\nu_{\mathrm{add}}$ is the measure $|a|^{1/2}$ times the pushforward of Lebesgue measure under the inverse of the mixed-space ring equivalence, and $\nu_{\mathrm{mul}}$ is a Haar measure on the unit group. **The archimedean Whittaker function.** $W_{\mathrm{arch}}$ is a function on $\mathrm{GL}_3$ of the infinite adèles, and `hWarch` is a conjunction of clauses, summarised here: $W_{\mathrm{arch}}\neq 0$; it is $K$-finite for the orthogonal subgroup `orth3`; it is continuous and satisfies a gauge decay bound of the form $\|W_{\mathrm{arch}}(g_\infty)\|\le C/\bigl((\prod_w \mathrm{archRoot}_1\mathrm{archRoot}_2)^t(1+\mathrm{archRootSum})^N\bigr)$ for some $t$, all $N$ and suitable $C$; it is a $\psi_\infty$-Whittaker function; it transforms under central scalars $z$ by $\omega_3(E z)$; for every admissible idèle character $\sigma$ of $\mathbb Q$ with archimedean parameters $(t,e)$ at all real places, and every $g_\infty$, there exists an entire function $P$ such that the zeta integral `archZeta30` for the right translate of $W_{\mathrm{arch}}$ by $g_\infty$ converges in a right half plane and equals $P(s)$ times the archimedean factor of the Hecke $L$-datum $\mathrm{heckeDatum}(K,\nu)$ with the parameters shifted by $(t,e)$, $P$ has exponential bounds $\|P(s)\|\le C e^{A|\Im s|}$ in vertical strips, the product $P\cdot\mathrm{archFactor}$ decays faster than any power of $|\Im s|$ in vertical strips, the dual zeta integral `archZeta31` for the dual Whittaker function converges in a half plane, and the functional equation
--   $$\mathrm{archZetaDual31}(1-s)=\Bigl(\prod_{w\ \mathrm{real}}\mathrm{signEpsilon}(a_R(w)+e)\cdot\prod_{w\ \mathrm{complex}} i^{|k_C(w)|}\cdot\prod_{w}\lambda_{\mathrm{arch}}(w)\Bigr)\bigl(\omega_3(Ea_\infty)\,\sigma(Ea_\infty)^3\bigr)|a|^{3(s-1/2)}P(s)\,\mathrm{archFactorDual}(1-s)$$
--   holds; finally, there is an admissible $\sigma$ and a point $s$ at which `archZeta30` of $W_{\mathrm{arch}}$ twisted by $\sigma\circ E$ is non-zero. **The cubic induction form.** $F$ is a `CubicInductionForm` for $K$, the additive character $\psi$ and the twist $\nu$, relative to the carrier pins `productionPinsOf` built from the class-representative Siegel set $\mathrm{classRepSiegelSet}\,\mathbb Q\,(1/2)\,1\,(1/2)\,2$, the level subgroups $\mathrm{levelOne}(N)\sqcap\mathrm{finiteAdelicGL2Subgroup}$, the Hecke generators and the adelic box; in particular $F$ carries a cusp form `form` on $\mathrm{GL}_3$ of the adèles, its Whittaker function, local Whittaker functions $F.\mathrm{whittakerLoc}\,v$ on $\mathrm{GL}_3(\mathbb Q_v)$, an archimedean Whittaker function, a central character, a dual Whittaker function, and the axioms of that structure. The hypotheses on $F$ are: `hF0`, that $F.\mathrm{form}\neq 0$ and that at every $v$ unramified in $K$ with $\mathrm{addCharLevel}(\mathrm{psiLoc}\,\psi\,v)=0$ one has $F.\mathrm{whittakerLoc}\,v\,(1)=1$ and $F.\mathrm{whittakerLoc}\,v$ has the spherical torus values attached to $\mathrm{inducedCoeff}(K,\nu)$; `hFc`, `hFw`, `hFdw`, continuity of `form`, `whittaker` and `dualWhittaker`; `hFg`, `hFdg`, gauge majorisation of `whittaker` and `dualWhittaker`; `hArchEq`, $F.\mathrm{whittakerArch}=W_{\mathrm{arch}}$; `hEss`, that at every bad place $v$ which is unramified in $K$ and at which $\mathrm{psiLoc}\,\psi\,v=(\mathrm{psiLocal}\,\mathbb Q\,v)^{-1}$, the cyclic subspace generated by the right translates of $F.\mathrm{whittakerLoc}\,v$ contains a non-zero $\mathrm{psiLoc}\,\psi\,v$-Whittaker function $W$, invariant under right translation by the congruence set $\mathrm{congruenceK1}$ of level $\mathrm{inducedLevelAt}(K,\nu,v)$, with $W(1)=1$ and the spherical torus values of $\mathrm{inducedCoeff}(K,\nu)$; and `hBad`, that for every finite set $T$ of finite places, at each bad $v\in T$ the function $F.\mathrm{whittakerLoc}\,v$ is right invariant under some open subgroup of $\mathrm{GL}_3(\mathbb Q_v)$, and each non-zero member $W$ of its cyclic subspace generates $F.\mathrm{whittakerLoc}\,v$ in turn. **Local admissibility, level and conductor growth.** `hW₃admM` requires, for each $p\in SQ$ and each open subgroup $U_v$ of $\mathrm{GL}_3(\mathbb Q_p)$, a finite set $B$ of functions on $\mathrm{GL}_3(\mathbb Q_p)$ such that every $U_v$-right-invariant element of the cyclic subspace generated by $g\mapsto \chi_{A,p}(\det g)\,F.\mathrm{whittakerLoc}\,p\,(g)$ lies in the complex span of $B$. The function $d_M$ on $SQ$ and the hypothesis `hlev0M` provide a principal-congruence level: for $p\in SQ$, $F.\mathrm{whittakerLoc}\,p$ is right invariant under those $k$ in the maximal compact subgroup $\mathrm{localMaximalCompact3}$ all of whose entries of $k-1$ have valuation at most $\exp(-d_M(p))$. Finally `hkβM` requires, for $p\in SQ$ and $b$ with $p^b\parallel\Phi.\mathrm{level}$, the inequality $6(b+3d_M(p)+3)+7\le k_\chi(p)$. **Conclusion.** Let $p$ be a finite place of $\mathbb Q$ with $p\in SQ$, let $b$ be a natural number with $p^b\mid\Phi.\mathrm{level}$ and $p^{b+1}\nmid\Phi.\mathrm{level}$, and let $\varpi_p$ be an element of the valuation ring of $\mathbb Q_p$ whose image $\varpi$ in $\mathbb Q_p$ is non-zero and has valuation $\exp(-1)$. Let $W$ be any element of the cyclic subspace $\mathrm{gl3CyclicSubspace}$ generated by the right translates of $g\mapsto \chi_{A,p}(\det g)\,F.\mathrm{whittakerLoc}\,p\,(g)$, let $g_3\in\mathrm{GL}_3(\mathbb Q_p)$, $k_0\in\mathrm{GL}_2(\mathbb Q_p)$, let $\eta$ be a character of $\mathbb Q_p^\times$ with conductor exponent $c\le b$, and, with the Borel measurable structures on $\mathbb Q_p$ and on $\mathrm{GL}_2(\mathbb Q_p)$, let $\mu_2$ be any Haar measure on $\mathrm{GL}_2(\mathbb Q_p)$. Then there exists a finite set $T\subseteq\mathbb Z\times\mathbb Z$ such that for every $n=(n_1,n_2)\notin T$ both of the following integrals vanish, the outer integral being over $\{u\in\mathbb Q_p^\times:|u|=1\}$ with respect to the pullback along $u\mapsto u$ of the multiplicative measure $\mathrm{mulMeasure}$ of the self-dual Haar measure at $p$, and the inner integral over the subgroup $\mathrm{localLevelOne}(p,p^{b})$ of $\mathrm{GL}_2(\mathbb Q_p)$ with respect to $\mu_2$:
--
--   (i) $\displaystyle\int_{|u|=1}\Bigl(\int_{\mathrm{localLevelOne}(p,p^{b})}W\bigl(\iota\bigl(\mathrm{scalarPi}(\varpi)^{n_2}\,\mathrm{diagUnitGL2}(\varpi^{n_1}u)\,(k_0k)\bigr)\,g_3\bigr)\,d\mu_2(k)\Bigr)\eta(u)\,du=0$, where $\iota$ is the block embedding $\mathrm{GL}_2\to\mathrm{GL}_3$, $\mathrm{scalarPi}(\varpi)=\mathrm{diag}(\varpi,\varpi)$ and $\mathrm{diagUnitGL2}(x)=\mathrm{diag}(x,1)$; (ii) the same integral with $W$ replaced by the dual Whittaker function $\mathrm{dualWhittakerFn3}$ of $x\mapsto W(x\,g_3)$, that is $x\mapsto W(\mathrm{longWeyl3}\cdot{}^t x^{-1}g_3)$, and with $k$ replaced by its transpose inverse $\mathrm{transposeInvN}$ in the inner argument:
--   $\displaystyle\int_{|u|=1}\Bigl(\int_{\mathrm{localLevelOne}(p,p^{b})}\mathrm{dualWhittakerFn3}\bigl(x\mapsto W(x g_3)\bigr)\bigl(\iota\bigl(\mathrm{scalarPi}(\varpi)^{n_2}\,\mathrm{diagUnitGL2}(\varpi^{n_1}u)\,(k_0\,{}^tk^{-1})\bigr)\bigr)d\mu_2(k)\Bigr)\eta(u)\,du=0.$
--
--   The statement expresses that the $(K_1(p^{b}),\eta)$-window of torus coefficients, taken along the embedding $\mathrm{GL}_2\hookrightarrow\mathrm{GL}_3$ and for the twisted local Whittaker data of a cubic induction form at a prime $p$ dividing the level, is supported in a finite subset of $\mathbb Z\times\mathbb Z$, for the function and for its dual simultaneously. It is the local input to the Rankin–Selberg analysis of the induced $\mathrm{GL}_3$ object, used by the theorem producing the entire, strip-bounded identification of the Rankin–Selberg integral with the archimedean factor times the $L$-function of the Rankin–Selberg datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_torusFinite_of_cubicInductionForm_twisted_noFE32_level.lean

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

theorem LanglandsTunnell.CubicInduction.forall_mem_gl3CyclicSubspace_torusFinite_of_cubicInductionForm_twisted_noFE32_level
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

    (kχ : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (hkχ : ∀ p ∈ SQ,
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p (NumberField.TateGlobal.localChar χA p) (kχ p))
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

    (hW₃admM : ∀ p : ↥SQ, ∀ Uv : Subgroup (LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ))), IsOpen (Uv : Set (LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)))) →
      ∃ B : Finset (LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)) → ℂ), ∀ W ∈ gl3CyclicSubspace
        (fun g : LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)) => ((NumberField.TateGlobal.localChar χA (p : HeightOneSpectrum (𝓞 ℚ)) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) g),
        (∀ k ∈ Uv, ∀ g : LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)), W (g * k) = W g) → W ∈ Submodule.span ℂ (B : Set (LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)) → ℂ)))

    (dM : ↥SQ → ℕ)
    (hlev0M : ∀ p : ↥SQ, ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ (p : HeightOneSpectrum (𝓞 ℚ)),
      (∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) i j -
          (1 : Matrix (Fin 3) (Fin 3) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) i j) ≤ WithZero.exp (-(dM p : ℤ))) →
      ∀ g : LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)), F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) (g * k) = F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) g)
    (hkβM : ∀ p : ↥SQ, ∀ b : ℕ,
      ((p : HeightOneSpectrum (𝓞 ℚ)).asIdeal ^ b ∣ Φ.level ∧ ¬ (p : HeightOneSpectrum (𝓞 ℚ)).asIdeal ^ (b + 1) ∣ Φ.level) →
        6 * (b + 3 * dM p + 3) + 7 ≤ kχ (p : HeightOneSpectrum (𝓞 ℚ))) :
    ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ SQ → ∀ b : ℕ, (p.asIdeal ^ b ∣ Φ.level ∧ ¬ p.asIdeal ^ (b + 1) ∣ Φ.level) →
      ∀ (ϖp : p.adicCompletionIntegers ℚ)
        (hπp : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖp ≠ 0),
        Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖp) = WithZero.exp (-1 : ℤ) →
      ∀ W ∈ gl3CyclicSubspace
          (fun g : LocalGL3 p => ((NumberField.TateGlobal.localChar χA p (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            F.whittakerLoc p g),
      ∀ (g₃ : LocalGL3 p) (k₀ : GL (Fin 2) (p.adicCompletion ℚ)) (η : (p.adicCompletion ℚ)ˣ →* ℂˣ)
      (c : ℕ),
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p η c → c ≤ b →
      letI := LanglandsTunnell.TateLocal.localBorel ℚ p
      letI := localGLBorel ℚ p
      haveI := borelSpace_localGLBorel ℚ p
      ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
        ∃ T : Finset (ℤ × ℤ), ∀ n : ℤ × ℤ, n ∉ T →
          (∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
              (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ (b)) :
                    Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
                  W (iotaGL (UnramifiedWhittaker.scalarPi
                        (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖp) hπp ^ n.2 *
                      diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖp) hπp
                        ^ n.1 * u) * (k₀ * k)) * g₃) ∂μ₂) * ((η u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ p)))) = 0 ∧
          (∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
              (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ (b)) :
                    Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
                  dualWhittakerFn3 (fun x => W (x * g₃)) (iotaGL (UnramifiedWhittaker.scalarPi
                        (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖp) hπp ^ n.2 *
                      diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖp) hπp
                        ^ n.1 * u) * (k₀ * AutomorphicForm.transposeInvN (Fin 2) k))) ∂μ₂) * ((η u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ p)))) = 0 := by sorry
