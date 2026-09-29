-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_rsGlobalIntegral_reference_eq_mul_rsArchIntegral_mul_rsFinIntegral_indicator_mul_of_finiteFamily_arch
-- name    : LanglandsTunnell.RankinSelberg.exists_ne_zero_forall_rsGlobalIntegral_reference_eq_mul_rsArchIntegral_mul_rsFinIntegral_indicator_mul_of_finiteFamily_arch
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/83f63851-c007-522f-8188-1be664f04be4
-- title:
--   Factorisation of the purified reference Rankin–Selberg integral
-- statement:
--   Throughout, $K$ is a number field whose ring of integers is an integral $\mathcal{O}_{\mathbb{Q}}$-algebra, and the hypothesis `_hdeg` asks that $[K:\mathbb{Q}]=3$. Further data: a Hecke eigensystem $\Phi$ over $\mathbb{Q}$ with complex coefficients (a nonzero level ideal together with functions $p\mapsto \Phi.a\,p$, $p\mapsto\Phi.b\,p$ on the finite places), a finite set $S_Q$ of finite places of $\mathbb{Q}$, a finite set $S_K$ of finite places of $K$, an archimedean parameter $P$ of type `RealArchParam` (either `principal` $(u_1,a_1,u_2,a_2)$ with $a_i\in\mathbb{Z}/2$, or `discrete` $(u_0,n)$ with $n\ge 1$), and a finite set $S\subseteq S_Q$. The hypothesis `hSQ` has two clauses: every $p$ with $\Phi.\mathrm{level}\le p$ lies in $S_Q$, and every prime $\mathfrak{P}$ of $K$ whose underlying prime of $\mathbb{Q}$ lies outside $S_Q$ has ramification index $1$; `hSK` says $\mathfrak{P}\in S_K$ exactly when the prime below it lies in $S_Q$; `hb` says $\|\Phi.b\,p\|=1$ off $S_Q$, and `ha` that $\sum_p\|\Phi.a\,p\|\,N(p)^{-\sigma}$ converges for every $\sigma>1$.
--
--   On the $GL_2$ side, $R$ is a `SmoothCuspRealizationAt` of $\Phi.\mathrm{toRawCentral}$ (the eigensystem with $b$ renormalised by $N(v)^{-1}$) for the pinned carrier `productionPinsGeneral ℚ`, with `hRc` the continuity of $R$, `hRS` the inclusion of its exceptional set in $S$, and $C_{\mathrm{fin}}$ an auxiliary function of a finite idele and an adelic matrix. The conditions `hP1`, `hP2` require, in the `principal` case, $|\mathrm{Re}(u_1-u_2)|<1$ and that $u_1-u_2$ not be a nonzero integer $p$ with $a_1-a_2=p+1$ in $\mathbb{Z}/2$; `hRcen` matches the archimedean component of $R$'s central character at the real place with exponent $P.\mathrm{centralExponent}+1$ and sign $P.\mathrm{centralSign}$. A family $\varphi_{\mathrm{par}}$, indexed by parities $\mathrm{par}:\mathrm{InfinitePlace}\,\mathbb{Q}\to\mathbb{Z}/2$, together with archimedean Whittaker functions $W_r$ and weights $k_w$, is subject to: `hiso` (each $\varphi_{\mathrm{par}}$ is an `IsIsotypicCuspFormAt` form of level $\Phi.\mathrm{level}$, exceptional set $S$, central character $R.\mathrm{centralChar}$ and Hecke eigenvalues $\Phi.a$), `hφne` (nonvanishing), `hφKf` (each is fixed by right convolution with some `IsFactorizableTestFn`), `hφarch` (at the real place it transforms by `archWeightCharAt` of weight $k_w$), `hkw1`, `hkw2` (the weight equals $\mathrm{signShift}(a_1+\mathrm{par}\,w)+\mathrm{signShift}(a_2+\mathrm{par}\,w)$ in the principal case, and $n+1$ in the discrete case), and `hφW` (for every idele $a$ and every $g$ in the finite adelic $GL_2$ subgroup, the `whittakerCoefficient` of $\varphi_{\mathrm{par}}$ at $1$ and at $\mathrm{diag}(a,1)g$ equals $\prod_w W_r(\mathrm{par},w)$ evaluated on the archimedean coordinates of $a$, times $C_{\mathrm{fin}}$ of the finite part of $a$ at $g$). The clauses `hWr1`–`hWr4` record the analytic behaviour of $W_r$: the reflection law $W_r(-t)=(-1)^{a_1}W_r(t)$ when $P$ is principal with equal signs and $\mathrm{par}\,w=a_1$; vanishing on $t<0$ in the discrete case; and, in the two remaining sign situations, convergence of the Mellin transform of $t\mapsto (W_r(t)+(-1)^{b}W_r(-t))/t$ on a right half-plane with value $\frac{2s+u_1+u_2-1}{4\pi}\,(P.\mathrm{twist}\,0\,a_1).\mathrm{archFactor}(s)$, respectively $(P.\mathrm{twist}\,0\,b).\mathrm{archFactor}(s)$.
--
--   The character data: a finite set $T_q$ of finite places of $\mathbb{Q}$ and an admissible twist $\omega$ of $K$ (idele class, continuous, unitary) which, by `hωT`, is unramified at every $\mathfrak{P}$ over a place outside $T_q$ with uniformiser value the base-change coefficient $(\mathrm{formalBaseChange}\ \mathbb{Q}\ K\ \Phi).b\,\mathfrak{P}$; `hE` places all $\mathfrak{P}$ over $T_q$ in $S_K$, and `hωR`, `hωC` prescribe the archimedean components of $\omega$ by the real and complex parameters attached to $P$. Next, an admissible twist $\mu$ of $K$ with `hoff`: there is no admissible twist $\eta$ of $\mathbb{Q}$ such that at every $\mathfrak{P}$ where $\mu$ and $\eta$ are unramified the uniformiser value of $\mu$ is $\eta$'s uniformiser value raised to the inertia degree; `hdepth` bounds $4(\mathrm{count}$ of the pushed level at $w+\mathrm{addCharLevel}+1)$ by the conductor exponent of $\mu$ at each $w\in S_K$. Further, an admissible twist $\chi_A$ of $\mathbb{Q}$, unramified off $S_Q$ (`hχoff`), with conductor exponents $k_\chi(p)$ at $p\in S_Q$ (`hkχ`) and trivial archimedean component (`hχinf`); a bound function $c_0$ with `hν` (at each $w$ above $p\in S_Q$ the local conductor exponent of $\mu\cdot(\chi_A\circ\text{idelic norm})^{-1}$ is some $c\le c_0(p)$); exponents $b_Q(p)$ exactly dividing the level (`hbQ`); and `hkfloor`, an explicit lower bound for $k_\chi(p)$ in terms of $b_Q(p)$, $c_0(p)$, the inertia degrees and ramification indices in the fibre over $p$, and the levels of the local standard additive characters. An admissible twist $\nu$ of $K$ satisfies $\mu=\nu\cdot(\chi_A\circ\text{idelic norm of }\mathrm{genuineBaseChange})$ (`hμν`). Archimedean data $u_R,a_R$ at the real places and $u_C,k_C$ at the complex places of $K$ describe the archimedean components of $\mu$ (`hcR`, `hcC`).
--
--   On the $GL_3$ side: a global additive character $\psi$ of the adeles of $\mathbb{Q}$ (`hψ`) whose local levels all vanish (`hlev`) and with $\psi^{-1}=\mathtt{psiQ}$ (`hψQ`); a `CubicInductionForm` $F$ for $K$, the pinned carrier (written out as `productionPinsOf` of the class-representative Siegel set, the level subgroups intersected with the finite adelic subgroup, the Hecke generators and the adelic box, i.e. `productionPinsGeneral ℚ`), $\psi$ and $\nu$. Its hypotheses are `hF0` ($F.\mathrm{form}\neq 0$, and at places unramified in $K$ with vanishing local character level the local Whittaker function takes value $1$ at the identity and has spherical torus values with coefficients $\mathrm{inducedCoeff}\,K\,\nu$), the continuity of $F.\mathrm{form}$, $F.\mathrm{whittaker}$, $F.\mathrm{dualWhittaker}$, the gauge majorisations `hFg`, `hFdg`, and `hBad`: for every finite set $T$, at every bad place $v\in T$ for $\nu$ the function $F.\mathrm{whittakerLoc}\,v$ is right invariant under some open subgroup, and it lies in the `gl3CyclicSubspace` generated by any nonzero member of its own cyclic subspace. A finite set $S'\supseteq S_Q$ satisfies `hgood`: no place outside $S'$ is bad for $\mu$. Local uniformisers $\varpi_p$ in the local integers are nonzero (`hπ`) of valuation $\exp(-1)$ (`hϖ`) off $S_Q$. For $p\in S_Q$, functions $m_P(p)$ on $GL_3(\mathbb{Q}_p)$ lie in the cyclic subspace of $g\mapsto \chi_{A,p}(\det g)\,F.\mathrm{whittakerLoc}\,p\,g$ (`hmPmem`), take value $1$ at the identity (`hmP1`), and satisfy admissibility (`hW₃admM`: for every open subgroup a finite set spans the invariants inside the cyclic subspace) and cyclicity (`hW₃irrM`). An element $h_{\mu f}$ of the finite adelic $GL_2$ subgroup is specified by `hhμf` as the product over $p\in S'\setminus S_Q$ of the place embeddings of the scalar matrix $\varpi_p$ raised to $-\mathrm{inducedLevelAt}\,K\,\mu\,p$. Functions $W_A$ on $GL_2(\mathbb{R})$ and $W_f$ on the finite adelic subgroup satisfy `hWAf` (the Whittaker coefficient of $\varphi_{\mathrm{par}}$ at $1$ splits as $W_A(\mathrm{ratArchGL2}\,g)\cdot W_f(\mathrm{finFactor}\,g)$), `hWfC` ($W_f=C_{\mathrm{fin}}(1)$) and `hWf1` ($W_f(1)\neq0$). The hypothesis `hV` states, for each parity and each $p\in S_Q$, that the local Whittaker space [`AutomorphicForm.WhittakerModel.localSpaceAt`](def/AutomorphicForm_WhittakerModelLocal.html#L19) of $\varphi_{\mathrm{par}}$ at $p$ is cyclic under right translation by any nonzero member, admissible, and smooth. Finally $w_0\in GL_2(\mathbb{Q})$ is the antidiagonal involution (`hw₀`), and $W_{fd}$ is defined by `hWfd` as the idele norm of the determinant times $W_f$ evaluated after the substitution $g_f\mapsto w_0\cdot{}^{t}\!g_f^{-1}$.
--
--   The frozen data at which the conclusion is stated: a parity $\mathrm{par}$, a place $p\in S_Q$, a member $w_{2b}$ of the local Whittaker space of $\varphi_{\mathrm{par}}$ at $p$, archimedean translates $h_A\in GL_2(\mathbb{R})$ and $h_{A3}\in GL_3$ of the infinite adeles, the adelic matrix $h_2=\mathrm{archRealGLAt}(h_A)$, and purification data consisting of $n_P$, coefficients $c_P$, elements $x_P(j)\in GL_2(\mathbb{Q}_p)$ and functions $w_A$, $w_f$, $w_p$. The conjunction `hfacts` has seven clauses: $w_f\circ\mathrm{finFactor}$ is invariant under right translation by place embeddings at $p$; $w_f$ is measurable; for $t$ with vanishing archimedean part, $w_f\circ\mathrm{finFactor}$ transforms under left translation by the unipotent $t$ by the factor $\psi^{-1}(t)\,\mathrm{psiLoc}\,\psi\,p\,(t_p)$; $w_p$ is a $\psi_p$-Whittaker function for the local unipotent subgroup; $w_p\neq0$; $w_p$ equals $|\det y|^{-1/2}$ times some member of the local Whittaker space of $\varphi_{\mathrm{par}}$ at $p$; and the $\psi^{-1}$-Whittaker coefficient at $1$ of the purified form $g\mapsto\sum_j c_P(j)\,\mathrm{detNorm}(g\cdot x_P(j))^{-1/2}\varphi_{\mathrm{par}}(g\cdot x_P(j)\cdot h_2)$ equals $w_p(\mathrm{localAt}\,p\,g)\cdot\bigl(w_A(\mathrm{ratArchGL2}\,g)\,w_f(\mathrm{finFactor}\,g)\bigr)$.
--
--   With $GL_2(\mathbb{R})$ carrying its Borel structure, the conclusion is universally quantified over Haar measures $\mu_{fH}$ on the finite adelic $GL_2$ subgroup, $\mu_{NA}$ on the real unipotent subgroup and $\mu_{NF}$ on the finite unipotent subgroup, together with two compatibilities: `_hsplit`, that the image of the adelic $GL_2$ Haar measure under $g\mapsto(\mathrm{ratArchGL2}\,g,\mathrm{finFactor}\,g)$ is $\mathrm{archMeasure}\times\mu_{fH}$, and `_hNsplit`, the analogous splitting of the adelic unipotent Haar measure into the pushforwards of $\mu_{NA}$ and $\mu_{NF}$. Under these, two assertions hold.
--
--   First, for every adelic $g$ the $\psi^{-1}$-Whittaker coefficient at $1$ of the purified form $g\mapsto\sum_j c_P(j)\,\mathrm{detNorm}(g\cdot x_P(j))^{-1/2}\,\varphi_{\mathrm{par}}(g\cdot x_P(j)\cdot h_2)$ is the pure tensor obtained by evaluating $M\mapsto|\det M|^{-1/2}W_A(\mathrm{par})(M h_A)$ at $\mathrm{ratArchGL2}\,g$ and $g_f\mapsto\sum_j c_P(j)\,\mathrm{ideleNorm}(\det(g_f\cdot x_P(j)))^{-1/2}\,W_f(\mathrm{par})(\mathrm{finFactor}(g_f\cdot x_P(j)))$ at $\mathrm{finFactor}\,g$, the place embedding at $p$ being understood in both products.
--
--   Second, for every finite adelic $GL_3$ element $h_3^f$ whose archimedean component, component at $p$ and components at all places outside $S_Q$ are trivial, every $h_3$ with archimedean component $h_{A3}$ and the same finite components as $h_3^f$, and every finite family of coefficients $d(j)$ and $GL_3$ elements $k(j)$ with trivial archimedean component and trivial component at every place $v\neq p$, there exist a constant $c\neq0$, a function $E$ and an abscissa $\sigma_E$ with $E(s)\neq0$ for $\mathrm{Re}\,s>\sigma_E$, such that for every set $D$ which is a fundamental domain for the group of global points acting on adelic $GL_2$ with respect to the adelic Haar measure there is an abscissa $\sigma$ beyond which, for all $s$ with $\mathrm{Re}\,s>\sigma$,
--   $$\mathrm{rsGlobalIntegral}\,D\,s\,\varphi^{\circ}\,\Theta\;=\;c\cdot \mathrm{rsArchIntegral}\,\mathrm{archMeasure}\,\mu_{NA}\,s\,\bigl(M\mapsto|\det M|^{-1/2}W_A(\mathrm{par})(Mh_A)\bigr)\,\bigl(M\mapsto F.\mathrm{whittakerArch}(\mathrm{archComponent3}(\iota(\mathrm{archRealGLAt}\,M))\cdot h_{A3})\bigr)\cdot \mathrm{rsFinIntegral}\,\mu_{fH}\,\mu_{NF}\,s\,\mathbf{1}_{C}W^{\circ}_f\,\mathbf{1}_{C}F_f\cdot E(s),$$
--   where: $\varphi^{\circ}$ is the purified form written with a trivial outer sum over `Fin 1` with coefficient $1$ and with the factor $\mathrm{placeEmbed}\ \mathbb{Q}\ p\ 1$ inserted, i.e. $g\mapsto\sum_j c_P(j)\,\mathrm{detNorm}(g\cdot 1\cdot x_P(j))^{-1/2}\varphi_{\mathrm{par}}(g\cdot 1\cdot x_P(j)\cdot h_2)$; $\Theta$ is $x\mapsto\sum_j d(j)\,\chi_A(\det(x k(j)))\,F.\mathrm{form}(x\,k(j)\,h_3)$; $\mathrm{rsGlobalIntegral}\,D\,s\,\varphi\,\Theta$ denotes $\int_D\varphi(g)\,\Theta(\iota g)\,\mathrm{detNorm}(g)^{s-1/2}\,dg$; $C$ is the cut set of those $g$ in the finite adelic $GL_2$ subgroup whose component at every $v\notin S_Q$ factors as an element of the image of [`AutomorphicForm.unipotentGL2Hom`](def/AutomorphicForm_ConstantTerm.html#L33) times an element of [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178); $W^{\circ}_f$ is the finite tensor factor of the first assertion, evaluated at $\mathrm{finFactor}$ of the argument; and $F_f$ is the function sending $g$ to the product of $\sum_j d(j)\,\chi_{A,p}(\det(y\cdot\mathrm{componentAt3}\,p\,(k(j))))\,F.\mathrm{whittakerLoc}\,p\,(y\cdot\mathrm{componentAt3}\,p\,(k(j)))$ evaluated at $y=\mathrm{iotaGL}(\mathrm{localAt}\,p\,g)$ with the finitely-supported product over all finite places $v$ of $1$ at $v=p$ and of $\chi_{A,v}(\det(\mathrm{componentAt3}\,v\,(\iota g)\cdot \mathrm{componentAt3}\,v\,h_3^f))\,F.\mathrm{whittakerLoc}\,v\,(\mathrm{componentAt3}\,v\,(\iota g)\cdot\mathrm{componentAt3}\,v\,h_3^f)$ otherwise, again evaluated at $\mathrm{finFactor}$ of the argument.
--
--   This is the Rankin–Selberg step for the pair $(GL_2,GL_3)$ in the converse-theorem route to Langlands–Tunnell: the global zeta integral of one purified member of the automorphic family against the cubic induction form is shown to split as a nonzero constant times an archimedean local integral, a finite local integral cut down to the level-one locus outside $S_Q$, and a factor non-vanishing on a right half-plane. It feeds the construction of combinations of pure translates whose global integral does not vanish.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_rsGlobalIntegral_reference_eq_mul_rsArchIntegral_mul_rsFinIntegral_indicator_mul_of_finiteFamily_arch.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
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
import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open MeasureTheory LanglandsTunnell.TateLocal in

open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.exists_ne_zero_forall_rsGlobalIntegral_reference_eq_mul_rsArchIntegral_mul_rsFinIntegral_indicator_mul_of_finiteFamily_arch
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
    (P : RealArchParam)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hS : S ⊆ SQ)
    (R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral) (hRc : Continuous R.toFun)
    (Cfin : FiniteAdeleRing (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hRS : R.exceptionalSet ⊆ S)
    (hP1 : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1)
    (hP2 : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₂ →
          ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2))
    (hRcen : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
        IsArchCompAt ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) w
          (P.centralExponent + 1) (P.centralSign.val : ℤ))
    (φv : (InfinitePlace ℚ → ZMod 2) → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (Wr : (InfinitePlace ℚ → ZMod 2) → InfinitePlace ℚ → ℂ → ℂ)
    (kw : (InfinitePlace ℚ → ZMod 2) → InfinitePlace ℚ → ℤ)
    (hiso : ∀ par, IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) R.centralChar Φ.level S Φ (φv par))
    (hφne : ∀ par, φv par ≠ 0)
    (hφKf : ∀ par, ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ (φv par) α = φv par)
    (hφarch : ∀ par, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
        HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (kw par w)) (φv par))
    (hkw1 : ∀ par, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₂ →
          (kw par w : ℂ) = signShift (a₁ + par w) + signShift (a₂ + par w))
    (hkw2 : ∀ par, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
        P = RealArchParam.discrete u₀ n hn → kw par w = (n : ℤ) + 1)
    (hφW : ∀ par, ∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g ∈ finiteAdelicGL2Subgroup ℚ →
        whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ (φv par) 1 (diagOne a * g)
          = (∏ w : InfinitePlace ℚ, Wr par w (extensionEmbedding w ((a : AdeleRing (𝓞 ℚ) ℚ).1 w)))
              * Cfin (a : AdeleRing (𝓞 ℚ) ℚ).2 g)
    (hWr1 : ∀ par, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₁ → par w = a₁ →
          ∀ t : ℝ, Wr par w (-t) = (-1 : ℂ) ^ a₁.val * Wr par w t)
    (hWr2 : ∀ par, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
        P = RealArchParam.discrete u₀ n hn → ∀ t : ℝ, t < 0 → Wr par w t = 0)
    (hWr3 : ∀ par, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₁ → par w = a₁ + 1 →
          ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
            MellinConvergent (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ a₁.val * Wr par w (-t)) / (t : ℂ)) s ∧
              mellin (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ a₁.val * Wr par w (-t)) / (t : ℂ)) s
                = (2 * s + u₁ + u₂ - 1) / (4 * (Real.pi : ℂ)) * (P.twist 0 a₁).archFactor s)
    (hWr4 : ∀ par, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (b : ZMod 2),
        (b = par w ∨ b = par w + P.centralSign) →
          ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
            MellinConvergent (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ b.val * Wr par w (-t)) / (t : ℂ)) s ∧
              mellin (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ b.val * Wr par w (-t)) / (t : ℂ)) s
                = (P.twist 0 b).archFactor s)
    (Tq : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hω : IsAdmissibleTwist K ω)
    (hωT : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∉ Tq →
      IsUnramifiedCharAt ω 𝔓 ∧
        ((ω (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) = (formalBaseChange ℚ K Φ).b 𝔓)
    (hE : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∈ Tq → 𝔓 ∈ SK)
    (hωR : ∀ (w : InfinitePlace K) (hw : w.IsReal),
      IsArchCompAt K ω w (archOfParamR K P w hw).centralExponent
        ((archOfParamR K P w hw).centralSign.val : ℤ))
    (hωC : ∀ (w : InfinitePlace K) (hw : w.IsComplex),
      IsArchCompAt K ω w (archOfParamC K P w hw).centralExponent (archOfParamC K P w hw).centralTwist)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (hoff : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
    (hdepth : ∀ w : ↥SK,
      4 * (FractionalIdeal.count K w.1
            ((Φ.level.map (algebraMap (𝓞 ℚ) (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) +
          LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w.1) + 1) ≤
        LanglandsTunnell.TateLocal.conductorExponentAt K w.1 (localChar μ w.1))
    (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχA : LanglandsTunnell.Converse.IsAdmissibleTwist ℚ χA)
    (hχoff : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → IsUnramifiedCharAt χA v)
    (kχ : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (hkχ : ∀ p ∈ SQ,
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p (NumberField.TateGlobal.localChar χA p) (kχ p))
    (hχinf : ∀ v : InfinitePlace ℚ, v.IsReal → LanglandsTunnell.Converse.IsArchCompAt ℚ χA v 0 0)
    (c₀ : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (hν : ∀ p ∈ SQ, ∀ w ∈ primeFibre ℚ K p, ∃ c : ℕ, c ≤ c₀ p ∧
      LanglandsTunnell.TateLocal.HasConductorExponentAt K w
        (NumberField.TateGlobal.localChar
          (μ * (χA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)⁻¹) w) c)
    (bQ : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (hbQ : ∀ p ∈ SQ, p.asIdeal ^ bQ p ∣ Φ.level ∧ ¬ p.asIdeal ^ (bQ p + 1) ∣ Φ.level)
    (hkfloor : ∀ p ∈ SQ,
      6 * ((bQ p : ℤ) + 3 * (2 * ((∑ᶠ w ∈ primeFibre ℚ K p,
              ((w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal : ℤ) *
                ((Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal : ℤ) *
                    (2 * ((52 : ℤ) + 3 * (c₀ p : ℤ)) +
                      LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w) + 2) +
                  (c₀ p : ℤ) + LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w) + 1)) +
            ((52 : ℤ) + 3 * (c₀ p : ℤ)))) + 3) + 7 ≤ (kχ p : ℤ))
    (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hνadm : LanglandsTunnell.Converse.IsAdmissibleTwist K ν)
    (hμν : μ = ν * χA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ)
    (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ)
    (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (hcR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (hcC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ)
    (hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ)
    (F : CubicInductionForm K (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ψ ν)
    (hF0 : F.form ≠ 0 ∧ ∀ v, ¬ IsRamifiedIn K v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
        F.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K ν) v (F.whittakerLoc v))
    (hFc : Continuous F.form) (hFw : Continuous F.whittaker) (hFdw : Continuous F.dualWhittaker)
    (hFg : IsGaugeMajorised3 ℚ F.whittaker) (hFdg : IsGaugeMajorised3 ℚ F.dualWhittaker)
    (hBad :
        ∀ T : Finset (HeightOneSpectrum (𝓞 ℚ)),
          (∀ v ∈ T, IsBadPlace K ν v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
            ∀ k ∈ Uv, ∀ g : LocalGL3 v, F.whittakerLoc v (g * k) = F.whittakerLoc v g) ∧
          (∀ v ∈ T, IsBadPlace K ν v → ∀ W ∈ gl3CyclicSubspace (F.whittakerLoc v), W ≠ 0 →
            F.whittakerLoc v ∈ gl3CyclicSubspace W))
    (S' : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSS' : SQ ⊆ S')
    (hgood : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S' → ¬ IsBadPlace K μ p)
    (ϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p.adicCompletionIntegers ℚ)
    (hπ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p) ≠ 0)
    (hϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) = WithZero.exp (-1 : ℤ))
    (mP : ∀ p : ↥SQ, LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)) → ℂ)
    (hmPmem : ∀ p : ↥SQ, mP p ∈ gl3CyclicSubspace
      (fun g : LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)) => ((NumberField.TateGlobal.localChar χA (p : HeightOneSpectrum (𝓞 ℚ)) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) g))
    (hmP1 : ∀ p : ↥SQ, mP p 1 = 1)
    (hW₃admM : ∀ p : ↥SQ, ∀ Uv : Subgroup (LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ))), IsOpen (Uv : Set (LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)))) →
      ∃ B : Finset (LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)) → ℂ), ∀ W ∈ gl3CyclicSubspace (mP p),
        (∀ k ∈ Uv, ∀ g : LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)), W (g * k) = W g) → W ∈ Submodule.span ℂ (B : Set (LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)) → ℂ)))
    (hW₃irrM : ∀ p : ↥SQ, ∀ W ∈ gl3CyclicSubspace (mP p), W ≠ 0 → mP p ∈ gl3CyclicSubspace W)
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
    (hV : ∀ par, ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ SQ →
      ((∀ W₀ ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
          W₀ ≠ 0 → ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
            W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => W₀ (g * h))) ∧
        (∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
          ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ), ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
            (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g) → W ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))) ∧
        (∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
          ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g)))
    (w₀ : GL (Fin 2) ℚ) (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) ℚ) = !![0, 1; 1, 0])
    (Wfd : (InfinitePlace ℚ → ZMod 2) → finiteAdelicGL2Subgroup ℚ → ℂ)
    (hWfd : ∀ par (gf : finiteAdelicGL2Subgroup ℚ), Wfd par gf =
      ((NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (gf : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) *
        Wf par (RSCarrier.finFactor (globalPoints (𝓞 ℚ) ℚ w₀ * transposeInvN (Fin 2) (gf : AdelicGL2 (𝓞 ℚ) ℚ))))
    (par : InfinitePlace ℚ → ZMod 2) (p : HeightOneSpectrum (𝓞 ℚ)) (hp : p ∈ SQ)
    (w₂b : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂b : w₂b ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par))

    (hA : GL (Fin 2) ℝ) (hA3 : GL (Fin 3) (InfiniteAdeleRing ℚ))
    (h₂ : AdelicGL2 (𝓞 ℚ) ℚ) (hh₂A : h₂ = archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) hA)

    (nP : ℕ) (cP : Fin nP → ℂ) (xP : Fin nP → GL (Fin 2) (p.adicCompletion ℚ))
      (wA : GL (Fin 2) ℝ → ℂ) (wf : finiteAdelicGL2Subgroup ℚ → ℂ) (wp : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hfacts :       (∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          wf (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ p x)) = wf (RSCarrier.finFactor g)) ∧
        Measurable wf ∧
        (∀ (t : AdeleRing (𝓞 ℚ) ℚ), t.1 = 0 →
          ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, wf (RSCarrier.finFactor (unipotentGL2 t * g)) =
            (ψ⁻¹ t * LanglandsTunnell.CubicInduction.psiLoc ψ p (t.2 p)) * wf (RSCarrier.finFactor g)) ∧
        (∀ (t : (p.adicCompletion ℚ)) (y : GL (Fin 2) (p.adicCompletion ℚ)),
          wp (UnramifiedWhittaker.unipotent t * y) = NumberField.StandardAddChar.psiLocal ℚ p t * wp y) ∧
        wp ≠ 0 ∧
        (∃ w₁ ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
          ∀ y : GL (Fin 2) (p.adicCompletion ℚ), wp y = ((modulus ((Matrix.GeneralLinearGroup.det y : ((p.adicCompletion ℚ))ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * w₁ y) ∧
        (∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ψ⁻¹
              (fun g : AdelicGL2 (𝓞 ℚ) ℚ => ∑ j, cP j * (((detNorm (g * UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * φv par (g * UnramifiedWhittaker.placeEmbed ℚ p (xP j) * h₂))) 1 g =
            wp (localAt ℚ p g) * (wA (ratArchGL2 g) * wf (RSCarrier.finFactor g))))
    [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)] :

    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
    ∀ (μfH : MeasureTheory.Measure (finiteAdelicGL2Subgroup ℚ)) [μfH.IsHaarMeasure]
      (μNA : MeasureTheory.Measure RSCarrier.realUnipotent) [μNA.IsHaarMeasure]
      (μNF : MeasureTheory.Measure RSCarrier.finUnipotent) [μNF.IsHaarMeasure]
      (_hsplit : MeasureTheory.Measure.map (fun g : AdelicGL2 (𝓞 ℚ) ℚ => (LanglandsTunnell.ratArchGL2 g, RSCarrier.finFactor g))
          (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) = RSCarrier.archMeasure.prod μfH)
      (_hNsplit : MeasureTheory.Measure.map
          (fun n : adelicUnipotent ℚ => (LanglandsTunnell.ratArchGL2 (n : AdelicGL2 (𝓞 ℚ) ℚ), RSCarrier.finFactor n))
          (unipotentHaar ℚ) =
        (MeasureTheory.Measure.map Subtype.val μNA).prod (MeasureTheory.Measure.map Subtype.val μNF)),

    (∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ψ⁻¹
          (fun g : AdelicGL2 (𝓞 ℚ) ℚ => ∑ j, cP j * (((detNorm (g * UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * φv par (g * UnramifiedWhittaker.placeEmbed ℚ p (xP j) * h₂))) 1 g =
        (fun M : GL (Fin 2) ℝ => ((((|(Matrix.GeneralLinearGroup.det M : ℝ)| : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))) * WA par (M * hA))) (ratArchGL2 g) *
          (fun gf : finiteAdelicGL2Subgroup ℚ => ∑ j, cP j *
            (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det
                ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j))) : ℂ) ^ (-(1 / 2 : ℂ)) *
              Wf par (RSCarrier.finFactor ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j)))) (RSCarrier.finFactor g)) ∧

    ∀ (h₃f : AdelicGL 3 (𝓞 ℚ) ℚ),
      (archComponent3 (𝓞 ℚ) ℚ h₃f = 1 ∧ componentAt3 (𝓞 ℚ) ℚ p h₃f = 1 ∧
        ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → componentAt3 (𝓞 ℚ) ℚ v h₃f = 1) →
    ∀ (h₃ : AdelicGL 3 (𝓞 ℚ) ℚ),
      (archComponent3 (𝓞 ℚ) ℚ h₃ = hA3 ∧ ∀ v : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ v h₃ = componentAt3 (𝓞 ℚ) ℚ v h₃f) →
    ∀ (m : ℕ) (d : Fin m → ℂ) (k : Fin m → AdelicGL 3 (𝓞 ℚ) ℚ),
      (∀ j, archComponent3 (𝓞 ℚ) ℚ (k j) = 1 ∧
        ∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ p → componentAt3 (𝓞 ℚ) ℚ v (k j) = 1) →
    ∃ (c : ℂ) (E : ℂ → ℂ) (σE : ℝ), c ≠ 0 ∧ (∀ s : ℂ, σE < s.re → E s ≠ 0) ∧
    ∀ D : Set (AdelicGL2 (𝓞 ℚ) ℚ),
      IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) →
      ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
        rsGlobalIntegral D s
            (fun g : AdelicGL2 (𝓞 ℚ) ℚ => ∑ i : Fin 1, (1 : ℂ) * ∑ j, cP j *
                (((detNorm (g * UnramifiedWhittaker.placeEmbed ℚ p (1 : GL (Fin 2) (p.adicCompletion ℚ)) * UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) *
                  φv par (g * UnramifiedWhittaker.placeEmbed ℚ p (1 : GL (Fin 2) (p.adicCompletion ℚ)) * UnramifiedWhittaker.placeEmbed ℚ p (xP j) * h₂)))
            (fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ∑ j, d j *
                (((χA (Matrix.GeneralLinearGroup.det (x * k j)) : ℂˣ) : ℂ) * F.form (x * k j * h₃))) =
          c * RSCarrier.rsArchIntegral RSCarrier.archMeasure μNA s (fun M : GL (Fin 2) ℝ => ((((|(Matrix.GeneralLinearGroup.det M : ℝ)| : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))) * WA par (M * hA))) (fun M : GL (Fin 2) ℝ => F.whittakerArch (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) M)) * hA3)) *
            RSCarrier.rsFinIntegral μfH μNF s
              ({g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                  localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g : finiteAdelicGL2Subgroup ℚ =>
                (fun gf : finiteAdelicGL2Subgroup ℚ => ∑ j, cP j *
            (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det
                ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j))) : ℂ) ^ (-(1 / 2 : ℂ)) *
              Wf par (RSCarrier.finFactor ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j)))) (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ))))
              ({g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                  localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g : finiteAdelicGL2Subgroup ℚ =>
                (fun g : finiteAdelicGL2Subgroup ℚ =>
            (fun y : LocalGL3 p => ∑ j, d j * (((NumberField.TateGlobal.localChar χA p (Matrix.GeneralLinearGroup.det (y * componentAt3 (𝓞 ℚ) ℚ p (k j))) : ℂˣ) : ℂ) * F.whittakerLoc p (y * componentAt3 (𝓞 ℚ) ℚ p (k j)))) (iotaGL (localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ))) *
            (∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
              (if v = p then (1 : ℂ) else
                ((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det
                    (componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * componentAt3 (𝓞 ℚ) ℚ v h₃f)) : ℂˣ) : ℂ) *
                  F.whittakerLoc v (componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * componentAt3 (𝓞 ℚ) ℚ v h₃f)))) (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ)))) *
            E s := by sorry
