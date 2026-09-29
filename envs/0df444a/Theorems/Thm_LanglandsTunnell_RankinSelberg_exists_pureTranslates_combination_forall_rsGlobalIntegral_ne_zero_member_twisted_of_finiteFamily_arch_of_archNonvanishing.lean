-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_pureTranslates_combination_forall_rsGlobalIntegral_ne_zero_member_twisted_of_finiteFamily_arch_of_archNonvanishing
-- name    : LanglandsTunnell.RankinSelberg.exists_pureTranslates_combination_forall_rsGlobalIntegral_ne_zero_member_twisted_of_finiteFamily_arch_of_archNonvanishing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/7ed6c761-f7d5-5702-89c5-07aa6dd25954
-- title:
--   Non-vanishing far right of a reference Rankin–Selberg integral
-- statement:
--   Setting. $K$ is a number field of degree $3$ over $\mathbb{Q}$ (the hypothesis `_hdeg` records $\operatorname{finrank}_{\mathbb{Q}} K = 3$), carrying an algebra structure of $\mathcal{O}_{\mathbb{Q}}$ on $\mathcal{O}_K$ which is integral. $\Phi$ is a Hecke eigensystem over $\mathbb{Q}$ with complex coefficients, i.e. a non-zero level ideal $\Phi.\mathrm{level} \subseteq \mathcal{O}_{\mathbb{Q}}$ together with Satake data $p \mapsto \Phi.a\,p$, $p \mapsto \Phi.b\,p$ indexed by the height-one spectrum of $\mathcal{O}_{\mathbb{Q}}$.
--
--   Finite bad sets and growth. $S_Q$ is a finite set of primes of $\mathcal{O}_{\mathbb{Q}}$ with, by `hSQ`, two properties: every $p$ dividing the level lies in $S_Q$, and every prime $\mathfrak{P}$ of $\mathcal{O}_K$ lying over a prime outside $S_Q$ is unramified ($e = 1$). The hypothesis `hb` asks $\|\Phi.b\,p\| = 1$ off $S_Q$, and `ha` asks that $\sum_p \|\Phi.a\,p\|\,N(p)^{-\sigma}$ converge for every real $\sigma > 1$. $S_K$ is the finite set of primes of $\mathcal{O}_K$ lying over $S_Q$ (`hSK`), and $S \subseteq S_Q$ is a further finite set.
--
--   Archimedean parameter. $P$ is a real archimedean parameter, i.e. either $\mathrm{principal}\,u_1\,a_1\,u_2\,a_2$ with $u_i \in \mathbb{C}$, $a_i \in \mathbb{Z}/2$, or $\mathrm{discrete}\,u_0\,n$ with $1 \le n$. The hypotheses `hP1` and `hP2` constrain the principal case: $|\mathrm{Re}(u_1 - u_2)| < 1$, and if $u_1 - u_2$ is a non-zero integer $p$ then $a_1 - a_2 \neq p + 1$ in $\mathbb{Z}/2$.
--
--   The reference realisation. $R$ is a smooth cuspidal realisation at the production pins of $\mathbb{Q}$ (Siegel-set fundamental domain $\mathrm{classRepSiegelSet}\,\mathbb{Q}\,(1/2)\,1\,(1/2)\,2$, level subgroups $N \mapsto \mathrm{levelOne} \sqcap \mathrm{finiteAdelicGL2Subgroup}$, Hecke generators $\mathrm{heckeGen}$, adelic box) for the raw central normalisation $\Phi.\mathrm{toRawCentral}$ of $\Phi$, with continuous underlying function (`hRc`) and exceptional set contained in $S$ (`hRS`); `hRcen` requires the central character of $R$, transported along $\mathrm{Subgroup.topEquiv}^{-1}$, to have archimedean component at each real place given by exponent $P.\mathrm{centralExponent} + 1$ and sign $P.\mathrm{centralSign}$. $C_{\mathrm{fin}}$ is a function of a finite idele and an adelic $\mathrm{GL}_2$-element.
--
--   The finite family of cusp forms. $\varphi_{\bullet}$ assigns to each parity vector $\mathrm{par} : \mathrm{InfinitePlace}\,\mathbb{Q} \to \mathbb{Z}/2$ a function on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$; $W_r$ assigns archimedean Whittaker functions of a real variable and $k_w$ integer weights. The hypotheses on the family: `hiso`, each $\varphi_{\mathrm{par}}$ is an isotypic cusp form at the production pins with central character $R.\mathrm{centralChar}$, level $\Phi.\mathrm{level}$, exceptional set $S$ and eigensystem $\Phi$ (smooth cuspidal, continuous, invariant under the level subgroup, Hecke eigenfunction with eigenvalue $\Phi.a\,v$ and central eigenvalue $\Phi.\mathrm{toRawCentral}.b\,v$ off $S$); `hφne`, each $\varphi_{\mathrm{par}} \neq 0$; `hφKf`, each $\varphi_{\mathrm{par}}$ is its own right convolution with a factorizable test function; `hφarch`, at each real place $\varphi_{\mathrm{par}}$ transforms under the weight character $\mathrm{archWeightCharAt}$ of weight $k_w(\mathrm{par},w)$; `hkw1` and `hkw2`, which pin the weights in terms of $P$: in the principal case $k_w(\mathrm{par},w) = \mathrm{signShift}(a_1 + \mathrm{par}\,w) + \mathrm{signShift}(a_2 + \mathrm{par}\,w)$, in the discrete case $k_w(\mathrm{par},w) = n + 1$; `hφW`, the factorisation of the $\psi_{\mathbb{Q}}$-Whittaker coefficient of $\varphi_{\mathrm{par}}$ at $\mathrm{diagOne}(a)\,g$, for $g$ in the finite adelic subgroup, as $\prod_w W_r(\mathrm{par},w)$ evaluated at the archimedean components of $a$ times $C_{\mathrm{fin}}$ of the finite component of $a$ and $g$; and `hWr1`–`hWr4`, the archimedean functional equations and Mellin identities for $W_r$: the parity relation $W_r(-t) = (-1)^{a_1} W_r(t)$ when $P$ is principal with $a_1 = a_2 = \mathrm{par}\,w$ (`hWr1`), vanishing on $t < 0$ in the discrete case (`hWr2`), and, in a right half-plane, convergence of the Mellin transform of $t \mapsto (W_r(t) + (-1)^{b}W_r(-t))/t$ together with its evaluation as $\frac{2s+u_1+u_2-1}{4\pi}\,(P.\mathrm{twist}\,0\,a_1).\mathrm{archFactor}(s)$ in the opposite-parity principal case (`hWr3`) and as $(P.\mathrm{twist}\,0\,b).\mathrm{archFactor}(s)$ for $b = \mathrm{par}\,w$ or $b = \mathrm{par}\,w + P.\mathrm{centralSign}$ (`hWr4`).
--
--   The idele class characters. $T_q$ is a finite set of primes of $\mathcal{O}_{\mathbb{Q}}$. $\omega$ is an admissible twist of $K$ (idele class character, continuous, unitary) whose local data off $T_q$ agree with the formal base change of $\Phi$ (`hωT`: unramified at $\mathfrak{P}$ and $\omega$ of the uniformizer idele equals $(\mathrm{formalBaseChange}\,\mathbb{Q}\,K\,\Phi).b\,\mathfrak{P}$), with the primes above $T_q$ contained in $S_K$ (`hE`) and archimedean components prescribed by $\mathrm{archOfParamR}$ at real places and $\mathrm{archOfParamC}$ at complex places (`hωR`, `hωC`). $\mu$ is a further admissible twist of $K$ which, by `hoff`, does not descend: there is no admissible twist $\eta$ of $\mathbb{Q}$ whose unramified local values match $\mu$ through the inertia degree at every prime where both are unramified. The hypothesis `hdepth` demands, at every $\mathfrak{P} \in S_K$, that the conductor exponent of $\mu$ at $\mathfrak{P}$ be at least $4$ times the count of the extended level plus the level of the standard additive character plus $1$.
--
--   $\chi_A$ is an admissible twist of $\mathbb{Q}$, unramified off $S_Q$ (`hχoff`), with conductor exponent $k_{\chi}(p)$ at each $p \in S_Q$ (`hkχ`) and trivial archimedean components at real places (`hχinf`). The function $c_0$ bounds, by `hν`, the conductor exponents at the primes above each $p \in S_Q$ of $\mu$ twisted by the inverse of $\chi_A$ pulled back along the idelic norm of the genuine base change. $b_Q(p)$ is the exact exponent of $p$ in $\Phi.\mathrm{level}$ (`hbQ`), and `hkfloor` is an explicit lower bound for $k_{\chi}(p)$ in terms of $b_Q(p)$, $c_0(p)$, the inertia degrees, ramification indices and additive character levels of the primes in the fibre above $p$. Finally $\nu$ is an admissible twist of $K$ with $\mu = \nu \cdot (\chi_A \circ \mathrm{idelicNorm})$ (`hμν`), and the archimedean components of $\mu$ are recorded by $u_R, a_R$ at real places and $u_C, k_C$ at complex places (`hcR`, `hcC`).
--
--   The additive character and the cubic-induction form. $\psi$ is a global additive character of $\mathbb{A}_{\mathbb{Q}}$ (`hψ`: trivial on principal adeles, continuous, non-trivial) all of whose local levels vanish (`hlev`), with $\psi^{-1} = \psi_{\mathbb{Q}}$ (`hψQ`). $F$ is a cubic-induction form on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ attached to the production pins, to $\psi$ and to $\nu$ (an automorphic, cuspidal-along-both-parabolics function with Whittaker function, local Whittaker functions, archimedean Whittaker function, central character, dual Whittaker function and the factorisation, sphericity, level-invariance, multiplicity-one, moderate-growth and moment properties of that structure). The hypotheses on $F$: `hF0`, $F.\mathrm{form} \neq 0$ and, at every unramified $v$ with vanishing local additive character level, $F.\mathrm{whittakerLoc}\,v\,1 = 1$ and the local Whittaker function has the spherical torus values of the induced coefficients of $\nu$; `hFc`, `hFw`, `hFdw`, continuity of the form, the Whittaker function and the dual Whittaker function; `hFg`, `hFdg`, gauge majorisation of both Whittaker functions; and `hBad`, for every finite set $T$ of primes, open right-invariance of $F.\mathrm{whittakerLoc}\,v$ and irreducibility of its cyclic $\mathrm{GL}_3$-span at the bad places of $T$.
--
--   Auxiliary finite data. $S' \supseteq S_Q$ is finite and no prime outside $S'$ is bad for $\mu$ (`hgood`). $\varpi$ picks at each $p$ an element of the valuation ring whose image is non-zero (`hπ`) and of valuation $\exp(-1)$ (`hϖ`) for $p \notin S_Q$. For each $p \in S_Q$, $m_P(p)$ is a function on $\mathrm{GL}_3(\mathbb{Q}_p)$ lying in the cyclic $\mathrm{GL}_3$-span of $g \mapsto \chi_{A,p}(\det g)\,F.\mathrm{whittakerLoc}\,p\,g$ (`hmPmem`), normalised by $m_P(p)(1) = 1$ (`hmP1`), with the admissibility property `hW₃admM` (for every open subgroup $U_v$ a finite spanning set for the $U_v$-invariant vectors in the cyclic span of $m_P(p)$) and the irreducibility property `hW₃irrM`. The element $h_{\mu f}$ of the finite adelic subgroup is the explicit product, over $p \in S' \setminus S_Q$, of the place embeddings of the scalar matrices $\varpi_p$ raised to the power $-\mathrm{inducedLevelAt}\,K\,\mu\,p$ (`hhμf`).
--
--   Split Whittaker data. $W_A$ and $W_f$ split the Whittaker coefficient of $\varphi_{\mathrm{par}}$ at the production pins into its archimedean and finite factors (`hWAf`), $W_f$ is given by $C_{\mathrm{fin}}$ at the trivial finite idele (`hWfC`) and $W_f(\mathrm{par},1) \neq 0$ (`hWf1`). The hypothesis `hV` records, at each $p \in S_Q$, that the local Whittaker space of $\varphi_{\mathrm{par}}$ at $p$ is irreducible (every non-zero vector generates), admissible (finite-dimensional invariants under every open subgroup) and smooth (every vector has an open stabiliser). $w_0$ is the element of $\mathrm{GL}_2(\mathbb{Q})$ with matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$, and $W_{fd}$ is the dual finite Whittaker function defined from $W_f$ by the idele norm of the determinant and the translate by $w_0$ composed with $g \mapsto {}^t g^{-1}$ (`hWfd`).
--
--   The distinguished place and archimedean non-vanishing. A parity vector $\mathrm{par}$ and a prime $p \in S_Q$ are fixed, together with an element $w_{2b}$ of the local Whittaker space of $\varphi_{\mathrm{par}}$ at $p$. The final hypothesis `hΨA` asserts that for every Haar measure $\mu_{NA}$ on the real unipotent subgroup of $\mathrm{GL}_2(\mathbb{R})$ there exist $h_A \in \mathrm{GL}_2(\mathbb{R})$, $h_{A3} \in \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q},\infty})$ and $\sigma \in \mathbb{R}$ such that the archimedean Rankin–Selberg integral in $s$ of the pair $\bigl(M \mapsto |\det M|^{-1/2} W_A(\mathrm{par})(M h_A),\; M \mapsto F.\mathrm{whittakerArch}(\iota(\mathrm{archRealGLAt}(M))\,h_{A3})\bigr)$ is holomorphic on $\{\mathrm{Re}\,s > \sigma\}$ and non-zero at some point of that half-plane.
--
--   Conclusion. Under these hypotheses there exist:
--
--   (i) $h_2 \in \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ with trivial component at $p$, i.e. $\mathrm{localAt}\,\mathbb{Q}\,p\,h_2 = 1$;
--
--   (ii) $h_3 \in \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ with trivial component at $p$, i.e. $\mathrm{componentAt3}\,p\,h_3 = 1$;
--
--   (iii) a natural number $n_P$, coefficients $c_P : \mathrm{Fin}\,n_P \to \mathbb{C}$, elements $x_P : \mathrm{Fin}\,n_P \to \mathrm{GL}_2(\mathbb{Q}_p)$, and functions $w_A$ on $\mathrm{GL}_2(\mathbb{R})$, $w_f$ on the finite adelic subgroup and $w_p$ on $\mathrm{GL}_2(\mathbb{Q}_p)$, such that: $w_f$ is blind to the place $p$, in the sense that $w_f(\mathrm{finFactor}(g\,\iota_p(x))) = w_f(\mathrm{finFactor}\,g)$ for all $x \in \mathrm{GL}_2(\mathbb{Q}_p)$ and all $g$; $w_f$ is measurable; $w_f$ obeys the finite unipotent law with the $p$-factor divided out, namely $w_f(\mathrm{finFactor}(u(t)g)) = \psi^{-1}(t)\,\psi_p(t_p)\,w_f(\mathrm{finFactor}\,g)$ for every adele $t$ with vanishing archimedean part; $w_p$ is a $\psi_p$-Whittaker function, $w_p(u(t)y) = \psi_{\mathbb{Q},p}(t)\,w_p(y)$, and $w_p \neq 0$; there is $w_1$ in the local Whittaker space of $\varphi_{\mathrm{par}}$ at $p$ with $w_p(y) = |\det y|_p^{-1/2} w_1(y)$ for all $y$; and the purified reference form
--   $$g \longmapsto \sum_j c_P(j)\,\|\det(g\,\iota_p(x_P(j)))\|^{-1/2}\,\varphi_{\mathrm{par}}(g\,\iota_p(x_P(j))\,h_2)$$
--   has pure-tensor $\psi^{-1}$-Whittaker coefficient: for every $g$, its Whittaker coefficient at $1$ equals $w_p(\mathrm{localAt}\,p\,g)\,\bigl(w_A(\mathrm{ratArchGL2}\,g)\,w_f(\mathrm{finFactor}\,g)\bigr)$;
--
--   (iv) further finite combination data: a natural number $n$, coefficients $c : \mathrm{Fin}\,n \to \mathbb{C}$ and elements $x : \mathrm{Fin}\,n \to \mathrm{GL}_2(\mathbb{Q}_p)$ on the $\mathrm{GL}_2$ side, and a natural number $m$, coefficients $d : \mathrm{Fin}\,m \to \mathbb{C}$ and elements $k : \mathrm{Fin}\,m \to \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ on the $\mathrm{GL}_3$ side, such that each $k_j$ has trivial archimedean component and trivial component at every prime $v \neq p$, and such that for every set $D \subseteq \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ which is a fundamental domain for the image of the global points with respect to the adelic Haar measure, and for every real $\sigma'$, there is $s \in \mathbb{C}$ with $\mathrm{Re}\,s > \sigma'$ at which the global Rankin–Selberg integral
--   $$\mathrm{rsGlobalIntegral}\,D\,s\Bigl(g \mapsto \sum_i c_i \sum_j c_P(j)\,\|\det(g\,\iota_p(x_i)\,\iota_p(x_P(j)))\|^{-1/2}\varphi_{\mathrm{par}}(g\,\iota_p(x_i)\,\iota_p(x_P(j))\,h_2)\Bigr)\Bigl(y \mapsto \sum_j d_j\,\chi_A(\det(y k_j))\,F.\mathrm{form}(y\,k_j\,h_3)\Bigr)$$
--   is non-zero. In particular the integral is not identically zero on any right half-plane.
--
--   This is the non-vanishing input for the Rankin–Selberg convolution of the $\mathrm{GL}_2$ family member $\varphi_{\mathrm{par}}$ against the cubic-induction $\mathrm{GL}_3$ form $F$: the reference $\mathrm{GL}_2$ form is first purified by a finite combination of $p$-adic translates so that its Whittaker coefficient is a pure tensor, and then the resulting global integral is shown to be non-zero arbitrarily far to the right. It is cited by the realisation step which produces, from these data, a factorisation of the global integral over a fundamental domain in the form required by the converse theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_pureTranslates_combination_forall_rsGlobalIntegral_ne_zero_member_twisted_of_finiteFamily_arch_of_archNonvanishing.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_pureTranslates_combination_forall_rsGlobalIntegral_ne_zero_member_twisted_of_finiteFamily_arch_of_archNonvanishing
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
    (hΨA :
      letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
      ∀ (μNA : Measure RSCarrier.realUnipotent) [μNA.IsHaarMeasure],
        ∃ (hA : GL (Fin 2) ℝ) (hA3 : GL (Fin 3) (InfiniteAdeleRing ℚ)) (σ : ℝ),
          DifferentiableOn ℂ
              (fun s : ℂ => RSCarrier.rsArchIntegral RSCarrier.archMeasure μNA s
                (fun M : GL (Fin 2) ℝ => ((((|(Matrix.GeneralLinearGroup.det M : ℝ)| : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))) * WA par (M * hA)))
                (fun M : GL (Fin 2) ℝ => F.whittakerArch (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) M)) * hA3)))
              {s : ℂ | σ < s.re} ∧
          ∃ s : ℂ, σ < s.re ∧
            RSCarrier.rsArchIntegral RSCarrier.archMeasure μNA s
                (fun M : GL (Fin 2) ℝ => ((((|(Matrix.GeneralLinearGroup.det M : ℝ)| : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))) * WA par (M * hA)))
                (fun M : GL (Fin 2) ℝ => F.whittakerArch (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) M)) * hA3)) ≠ 0) :
    ∃ (h₂ : AdelicGL2 (𝓞 ℚ) ℚ), localAt ℚ p h₂ = 1 ∧
    ∃ (h₃ : AdelicGL 3 (𝓞 ℚ) ℚ), componentAt3 (𝓞 ℚ) ℚ p h₃ = 1 ∧
    ∃ (nP : ℕ) (cP : Fin nP → ℂ) (xP : Fin nP → GL (Fin 2) (p.adicCompletion ℚ))
      (wA : GL (Fin 2) ℝ → ℂ) (wf : finiteAdelicGL2Subgroup ℚ → ℂ) (wp : GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
      (∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
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
          wp (localAt ℚ p g) * (wA (ratArchGL2 g) * wf (RSCarrier.finFactor g))) ∧
    ∃ (n : ℕ) (c : Fin n → ℂ) (x : Fin n → GL (Fin 2) (p.adicCompletion ℚ))
      (m : ℕ) (d : Fin m → ℂ) (k : Fin m → AdelicGL 3 (𝓞 ℚ) ℚ),
      (∀ j, archComponent3 (𝓞 ℚ) ℚ (k j) = 1 ∧
        ∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ p → componentAt3 (𝓞 ℚ) ℚ v (k j) = 1) ∧
      ∀ D : Set (AdelicGL2 (𝓞 ℚ) ℚ),
        IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D
            (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) →
        ∀ σ' : ℝ, ∃ s : ℂ, σ' < s.re ∧
          rsGlobalIntegral D s
              (fun g : AdelicGL2 (𝓞 ℚ) ℚ => ∑ i, c i * ∑ j, cP j *
                (((detNorm (g * UnramifiedWhittaker.placeEmbed ℚ p (x i) * UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) *
                  φv par (g * UnramifiedWhittaker.placeEmbed ℚ p (x i) * UnramifiedWhittaker.placeEmbed ℚ p (xP j) * h₂)))
              (fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ∑ j, d j *
                (((χA (Matrix.GeneralLinearGroup.det (x * k j)) : ℂˣ) : ℂ) * F.form (x * k j * h₃))) ≠ 0 := by sorry
