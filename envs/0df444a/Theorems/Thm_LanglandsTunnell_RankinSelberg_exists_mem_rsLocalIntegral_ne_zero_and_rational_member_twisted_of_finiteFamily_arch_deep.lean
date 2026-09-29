-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_mem_rsLocalIntegral_ne_zero_and_rational_member_twisted_of_finiteFamily_arch_deep
-- name    : LanglandsTunnell.RankinSelberg.exists_mem_rsLocalIntegral_ne_zero_and_rational_member_twisted_of_finiteFamily_arch_deep
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/4997c43b-41ae-50fc-8992-7188cad677f9
-- title:
--   A non-vanishing rational local Rankin–Selberg pair at a level prime
-- statement:
--   The setting is as follows. $K$ is a number field with $[K:\mathbb{Q}]=3$, equipped with an algebra structure of $\mathcal{O}_{\mathbb{Q}}$ on $\mathcal{O}_K$ which is integral, and $\Phi$ is a Hecke eigensystem over $\mathbb{Q}$ with complex coefficients (a nonzero level ideal together with coefficient functions $\Phi.a$, $\Phi.b$ on the finite places).
--
--   Finite sets of places and growth. $SQ$ is a finite set of primes of $\mathcal{O}_{\mathbb{Q}}$ and `hSQ` has two clauses: every prime $p$ with $\Phi.\mathrm{level}\le p$ lies in $SQ$, and every prime $\mathfrak{P}$ of $\mathcal{O}_K$ whose restriction to $\mathbb{Q}$ is outside $SQ$ has ramification index $1$. `hb` requires $\|\Phi.b\,p\|=1$ for $p\notin SQ$, and `ha` requires, for each $\sigma>1$, summability of $p\mapsto\|\Phi.a\,p\|\,N(p)^{-\sigma}$. $SK$ is a finite set of primes of $\mathcal{O}_K$ with `hSK`: $\mathfrak{P}\in SK$ exactly when $\mathfrak{P}$ lies over a prime of $SQ$. $S\subseteq SQ$ is a further finite set.
--
--   Archimedean parameter. $P$ is a real archimedean parameter, either principal $(u_1,a_1,u_2,a_2)$ with $a_i\in\mathbb{Z}/2$ or discrete $(u_0,n)$ with $n\ge 1$. The genericity hypotheses `hP1` and `hP2` require, at a real infinite place, that in the principal case $|\operatorname{Re}(u_1-u_2)|<1$ and that for no nonzero integer $m$ with $u_1-u_2=m$ is $a_1-a_2=m+1$ in $\mathbb{Z}/2$.
--
--   The realisation. $R$ is a smooth cuspidal realisation on the production pins of $\mathbb{Q}$ for the eigensystem $\Phi.\mathrm{toRawCentral}$ (the same level and $a$-coefficients, with $b$-coefficients divided by the absolute norms), `hRc` asserts continuity of $R.\mathrm{toFun}$, `hRS` that $R.\mathrm{exceptionalSet}\subseteq S$, and $C_{\mathrm{fin}}$ is a function of a finite adele and an adelic $\mathrm{GL}_2$ element. By `hRcen`, at each real infinite place $w$ of $\mathbb{Q}$ the central character of $R$, transported along the identification of the full subgroup with the idele units, has archimedean component at $w$ of exponent $P.\mathrm{centralExponent}+1$ and sign exponent $P.\mathrm{centralSign}$.
--
--   The finite family of test vectors. For each parity vector $\mathrm{par}\colon \mathrm{InfinitePlace}\,\mathbb{Q}\to\mathbb{Z}/2$ there are given an adelic function $\varphi_{\mathrm{par}}$, archimedean Whittaker factors $W_r(\mathrm{par},w,\cdot)$ and weights $k_w(\mathrm{par},w)\in\mathbb{Z}$. The hypotheses on this family are: `hiso`, that $\varphi_{\mathrm{par}}$ is an isotypic cusp form on the production pins with central character $R.\mathrm{centralChar}$, level $\Phi.\mathrm{level}$ and exceptional set $S$ for $\Phi$ (smooth cuspidal automorphic, continuous, right invariant under the level subgroup, Hecke coset eigenfunction with eigenvalue $\Phi.a\,v$ and central eigenvalue $\Phi.\mathrm{toRawCentral}.b\,v$ off $S$); `hφne`, that $\varphi_{\mathrm{par}}\neq 0$; `hφKf`, that $\varphi_{\mathrm{par}}$ is reproduced by right convolution with some factorizable test function; `hφarch`, that $\varphi_{\mathrm{par}}$ satisfies the predicate `HasArchCharacterAt₀` at each real place $w$ with respect to `archWeightCharAt hw (kw par w)`, the $k_w(\mathrm{par},w)$-th power of the weight-one character attached to $w$; `hkw1` and `hkw2`, which pin these weights to $P$, namely $k_w(\mathrm{par},w)=\mathrm{signShift}(a_1+\mathrm{par}\,w)+\mathrm{signShift}(a_2+\mathrm{par}\,w)$ in the principal case and $k_w(\mathrm{par},w)=n+1$ in the discrete case; and `hφW`, the factorisation of the first Whittaker coefficient of $\varphi_{\mathrm{par}}$ with respect to the standard additive character of $\mathbb{Q}$: for every idele unit $a$ and every $g$ in the finite adelic $\mathrm{GL}_2$ subgroup, that coefficient at $\mathrm{diagOne}(a)\,g$ equals $\prod_w W_r(\mathrm{par},w,\cdot)$ evaluated at the embedded archimedean components of $a$, times $C_{\mathrm{fin}}$ of the finite part of $a$ at $g$. The four hypotheses `hWr1`–`hWr4` describe the archimedean factors at a real place: a reflection law $W_r(-t)=(-1)^{a_1}W_r(t)$ in the principal case with $a_1=a_2$ and $\mathrm{par}\,w=a_1$; vanishing on the negative reals in the discrete case; and, on suitable right half-planes, Mellin convergence together with an evaluation of the Mellin transform of $t\mapsto (W_r(t)+(-1)^{b}W_r(-t))/t$, equal to $\frac{2s+u_1+u_2-1}{4\pi}\,(P.\mathrm{twist}\,0\,a_1).\mathrm{archFactor}\,s$ in the principal case with $a_1=a_2$ and $\mathrm{par}\,w=a_1+1$, and equal to $(P.\mathrm{twist}\,0\,b).\mathrm{archFactor}\,s$ whenever $b=\mathrm{par}\,w$ or $b=\mathrm{par}\,w+P.\mathrm{centralSign}$.
--
--   Characters over $K$. $Tq$ is a finite set of primes of $\mathbb{Q}$ and $\omega$ an idele class character of $K$ which is admissible (idele class invariant, continuous, unitary); by `hωT`, at each $\mathfrak{P}$ lying over a prime outside $Tq$ the character $\omega$ is unramified and its value on the uniformizer idele is the $b$-coefficient at $\mathfrak{P}$ of the formal base change of $\Phi$ to $K$, while `hE` puts every $\mathfrak{P}$ over $Tq$ into $SK$; `hωR` and `hωC` prescribe the archimedean components of $\omega$ at real and complex places through $P$ and its base change. Next, $\mu$ is an admissible idele class character of $K$ subject to: `hoff`, the non-existence of an admissible idele class character $\eta$ of $\mathbb{Q}$ matching $\mu$ on uniformizers, i.e. with $\mu(\varpi_{\mathfrak{P}})=\eta(\varpi_{p})^{f(\mathfrak{P}/p)}$ at all $\mathfrak{P}$ where both are unramified; and `hdepth`, the depth bound $4\bigl(\mathrm{mult}_w(\Phi.\mathrm{level}\,\mathcal{O}_K)+\mathrm{addCharLevel}(\psi_{K,w})+1\bigr)\le \mathrm{conductorExponentAt}\,w(\mu_w)$ for each $w\in SK$.
--
--   The deep twist over $\mathbb{Q}$. $\chi_A$ is an admissible idele class character of $\mathbb{Q}$, unramified outside $SQ$ (`hχoff`), with conductor exponent $k_\chi(p)$ at each $p\in SQ$ (`hkχ`) and trivial archimedean component $(0,0)$ at real places (`hχinf`). The function $c_0$ bounds, by `hν`, the conductor exponent at each $w$ over $p\in SQ$ of the local component of $\mu\cdot(\chi_A\circ\mathrm{idelicNorm})^{-1}$. The function $b_{\mathbb{Q}}$ records by `hbQ` the exact exponent of $p$ in $\Phi.\mathrm{level}$ for $p\in SQ$, and `hkfloor` is the explicit lower bound
--   $$6\Bigl(b_{\mathbb{Q}}(p)+3\bigl(2\sum_{w\mid p}f_w\bigl(e_w(2(52+3c_0(p))+\mathrm{addCharLevel}(\psi_{K,w})+2)+c_0(p)+\mathrm{addCharLevel}(\psi_{K,w})+1\bigr)+(52+3c_0(p))\bigr)+3\Bigr)+7\le k_\chi(p)$$
--   for $p\in SQ$, where $e_w,f_w$ are the ramification index and inertia degree of $w$ over $p$. Finally $\nu$ is an admissible idele class character of $K$ with $\mu=\nu\cdot(\chi_A\circ\mathrm{idelicNorm})$ (`hμν`), and $u_R,a_R,u_C,k_C$ record by `hcR`, `hcC` the archimedean components of $\mu$ at the real and complex places of $K$.
--
--   The additive character and the cubic induction form. $\psi$ is a global additive character of the adeles of $\mathbb{Q}$ (principal invariant, continuous, nontrivial), with all local levels zero (`hlev`) and $\psi^{-1}$ the standard character $\psi_{\mathbb{Q}}$ (`hψQ`). $F$ is a cubic induction form for $K$ on the production pins of $\mathbb{Q}$ with respect to $\psi$ and $\nu$. The hypotheses on $F$ are: `hF0`, that $F.\mathrm{form}\neq 0$ and that at every $v$ unramified in $K$ with local additive level zero one has $F.\mathrm{whittakerLoc}\,v\,1=1$ and $F.\mathrm{whittakerLoc}\,v$ has spherical torus values for the induced coefficients of $\nu$; the continuity hypotheses `hFc`, `hFw`, `hFdw` for the form, its Whittaker function and its dual Whittaker function; the gauge majorisation hypotheses `hFg`, `hFdg` for the latter two (vanishing off a root-level region, with rapid-decay bounds there); and `hBad`, which asserts for every finite set $T$ of primes of $\mathbb{Q}$ both that at each $v\in T$ which is a bad place for $\nu$ the local Whittaker function $F.\mathrm{whittakerLoc}\,v$ is right invariant under some open subgroup of $\mathrm{GL}_3(\mathbb{Q}_v)$, and that it lies in the cyclic subspace generated by any nonzero element of its own cyclic subspace.
--
--   Auxiliary local data. $S'$ is a finite set of primes containing $SQ$ with $\mu$ having no bad place outside $S'$ (`hgood`); $\varpi$ assigns to each $p$ a local integer which, for $p\notin SQ$, is nonzero (`hπ`) of valuation $\exp(-1)$ (`hϖ`), hence a uniformizer. For each $p\in SQ$ a function $m_p$ on $\mathrm{GL}_3(\mathbb{Q}_p)$ is given, lying in the $\mathrm{GL}_3$ cyclic subspace generated by $g\mapsto \chi_{A,p}(\det g)\,F.\mathrm{whittakerLoc}\,p\,g$ (`hmPmem`), normalised by $m_p(1)=1$ (`hmP1`), whose cyclic subspace is admissible (`hW₃admM`: for each open subgroup a finite set spanning its invariants) and irreducible (`hW₃irrM`: $m_p$ lies in the cyclic subspace of any nonzero member of its cyclic subspace). An element $h_{\mu f}$ of the finite adelic $\mathrm{GL}_2$ subgroup is given whose underlying matrix is the product over $p\in S'\setminus SQ$ of the place embeddings of $\mathrm{scalarPi}(\varpi_p)^{-\mathrm{inducedLevelAt}_K(\mu,p)}$ (`hhμf`). Splitting data $W_A$, $W_f$ are given with `hWAf`, the factorisation of the first Whittaker coefficient of $\varphi_{\mathrm{par}}$ as $W_A(\mathrm{par},\mathrm{ratArchGL2}\,g)\cdot W_f(\mathrm{par},\mathrm{finFactor}\,g)$, with `hWfC` identifying $W_f$ with $C_{\mathrm{fin}}$ at the trivial finite idele, and with `hWf1`, $W_f(\mathrm{par},1)\neq 0$. The hypothesis `hV` states, for each parity and each $p\in SQ$, that the local Whittaker space of $\varphi_{\mathrm{par}}$ at $p$ is irreducible, admissible and smooth in the three senses: every nonzero member generates it under right translation, for each open subgroup its invariants are finitely spanned, and each member is right invariant under some open subgroup. Further, $w_0\in\mathrm{GL}_2(\mathbb{Q})$ is the antidiagonal involution $\begin{pmatrix}0&1\\1&0\end{pmatrix}$, and $W_{fd}$ is defined from $W_f$ by `hWfd`: $W_{fd}(\mathrm{par},g_f)=\|\det g_f\|\,W_f(\mathrm{par},\mathrm{finFactor}(w_0\cdot{}^{t}g_f^{-1}))$, the norm being the idele norm.
--
--   The member. A parity vector $\mathrm{par}$ and a prime $p\in SQ$ are fixed, together with a function $w_{2b}$ on $\mathrm{GL}_2(\mathbb{Q}_p)$ lying in the local Whittaker space of $\varphi_{\mathrm{par}}$ at $p$ (`hw₂b`), nonzero (`hw₂b0`), satisfying the $\psi_p$-Whittaker law $w_{2b}(u(x)g)=\psi_{\mathbb{Q},p}(x)\,w_{2b}(g)$ (`hw₂blaw`) and right invariant under the local level-one subgroup of level $\Phi.\mathrm{level}$ at $p$ (`hw₂bK`). An integer $d_p$ is given for which (`hπ₀levMp`) the cyclic subspace of $m_p$ contains a nonzero $W'$ such that, for every $k$ in the local maximal compact of $\mathrm{GL}_3(\mathbb{Q}_p)$ with all entries of $k-1$ of valuation at most $\exp(-d_p)$, the function $g\mapsto\chi_{A,p}(\det g)^{-1}W'(g)$ is unchanged by right translation by $k$; and `hkCMp` requires $6(b_{\mathbb{Q}}(p)+3d_p+3)+7\le k_\chi(p)$.
--
--   The identification hypothesis `hlamMIdp` provides a constant $\lambda_p\in\mathbb{C}$ with the following property. For every $b\in\mathbb{N}$ such that $2e_w b+1\le \mathrm{conductorExponentAt}_K\,w(\mu_w)$ for all $w$ over $p$, every local character $\eta$ of $\mathbb{Q}_p^\times$ with conductor exponent $c_\eta\le b$, every admissible idele class character $\eta_A$ of $\mathbb{Q}$ whose local component at $p$ is $\eta$ and whose composite with the idelic norm of $K/\mathbb{Q}$ is admissible, and every $g\in\mathrm{GL}_3(\mathbb{Q}_p)$, there are polynomials $Q_1,Q_2\in\mathbb{C}[X]$ with $Q_2\neq 0$, an integer $n$ and reals $\sigma_0,\sigma_1$ such that, with respect to the multiplicative measure induced from the self-dual additive Haar measure at $p$: the $\mathrm{GL}_3\times\mathrm{GL}_1$ zeta integrand of $m_p$ against $\eta$ is integrable for $\operatorname{Re}s>\sigma_0$, and there $\mathrm{localZeta30}(m_p,\eta,s,g)\cdot Q_2(N(p)^{-s})=Q_1(N(p)^{-s})\,N(p)^{ns}$; the dual integrand, formed from $\mathrm{dualWhittakerFn3}(m_p)$ and $\eta^{-1}$ at $\mathrm{weylPrime3}\cdot{}^{t}g^{-1}$, is integrable for $\sigma_1<\operatorname{Re}(1-s)$, and there $\mathrm{localZetaDual31}(m_p,\eta,1-s,g)\cdot Q_2(N(p)^{-s})$ equals $Q_1(N(p)^{-s})\,N(p)^{ns}$ multiplied by $\lambda_p$, by $\prod_{w\mid p}\bigl((\eta_A\circ\mathrm{idelicNorm})\cdot\mu\bigr)_w(-1)$, and by $\prod_{w\mid p}\mathrm{stdRootNumberAt}_K\,w\bigl(((\eta_A\circ\mathrm{idelicNorm})\cdot\mu)_w\bigr)\cdot N(w)^{(1/2-s)\,\mathrm{pinnedExp}}$, where $\mathrm{pinnedExp}$ is the conductor exponent plus the additive character level at $w$.
--
--   The last hypothesis `hβMp` is a finite-support statement: for every $b$ with $p^b$ exactly dividing $\Phi.\mathrm{level}$, every uniformizer $\varpi_p$ at $p$, every $g_3\in\mathrm{GL}_3(\mathbb{Q}_p)$, every $k_0\in\mathrm{GL}_2(\mathbb{Q}_p)$, every local character $\eta$ of conductor exponent $c\le b$ and every Haar measure $\mu_2$ on $\mathrm{GL}_2(\mathbb{Q}_p)$, there is a finite subset $T\subseteq\mathbb{Z}\times\mathbb{Z}$ outside of which both of the two iterated integrals vanish: the integral over the units of valuation $1$, weighted by $\eta$, of the integral over the local level-one subgroup of level $p^{b}$ of $m_p$ evaluated at $\iota(\mathrm{scalarPi}(\varpi_p)^{n_2}\,\mathrm{diagUnitGL2}(\varpi_p^{n_1}u)\,k_0k)\,g_3$, and the corresponding integral with $m_p(\cdot\,g_3)$ replaced by its dual Whittaker function and $k$ by ${}^{t}k^{-1}$.
--
--   Conclusion. With the Borel structure on $\mathrm{GL}_2(\mathbb{Q}_p)$: for every Haar measure $\mu_2$ on $\mathrm{GL}_2(\mathbb{Q}_p)$ and every Haar measure $\mu_{N_2}$ on the range of the unipotent homomorphism of $\mathbb{Q}_p$ into $\mathrm{GL}_2(\mathbb{Q}_p)$, there exist $w_2$ in the span of the right translates of $g\mapsto \mathrm{modulus}(\det g)^{-1/2}\,w_{2b}(g)$ and $W_3$ in the $\mathrm{GL}_3$ cyclic subspace of $m_p$ such that the following two assertions hold, all local Rankin–Selberg integrals being taken with respect to $\mu_2$ weighted by the quotient density of the unipotent subgroup for $\mu_{N_2}$, with modular function $g\mapsto\mathrm{modulus}(\det g)$ and exponent $s-1/2$.
--
--   First, there is a real $\sigma$ such that for all $s$ with $\operatorname{Re}s>\sigma$ the integral $\mathrm{rsLocalIntegral}$ formed from $g\mapsto W_3(\iota(g))$ and $w_2$ at $s$ is nonzero.
--
--   Second, there exist polynomials $P_0,P_{d0},Q_0,Q_{d0}\in\mathbb{C}[X]$, integers $m_0,m_{d0}$ and reals $\sigma_2,\sigma_3$ with $P_0\neq 0$ and $Q_{d0}\neq 0$ such that: for all $s$ with $\operatorname{Re}s>\sigma_2$, the integral formed from $g\mapsto W_3(\iota(g))$ and $w_2$ at $s$, multiplied by $Q_0(N(p)^{-s})$, equals $N(p)^{m_0 s}P_0(N(p)^{-s})$; and for all $s$ with $\operatorname{Re}s>\sigma_3$, the dual integral — formed from $g\mapsto \mathrm{dualWhittakerFn3}(W_3)(\iota(g))$ and from $g\mapsto \mathrm{modulus}(\det g)\,w_2\bigl((w_0)_p\,{}^{t}g^{-1}\bigr)$, where $(w_0)_p$ is the component at $p$ of the global point $w_0$ — multiplied by $Q_{d0}(N(p)^{-s})$, equals $N(p)^{m_{d0} s}P_{d0}(N(p)^{-s})$.
--
--   This is the local half, at a prime $p$ dividing the level, of the non-degeneracy input to the Rankin–Selberg $\gamma$-factor construction: it produces a Jacquet–Piatetski-Shapiro–Shalika test pair for the local $\mathrm{GL}_3\times\mathrm{GL}_2$ convolution at $p$ whose zeta integral is nonvanishing on a right half-plane and whose primal and dual integrals are rational functions of $N(p)^{-s}$ up to a monomial. It is used by [`LanglandsTunnell.RankinSelberg.exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi`](thm.html#LanglandsTunnell.RankinSelberg.exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi), which assembles the local data at the members of the finite family into the global functional-equation argument of the converse theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_mem_rsLocalIntegral_ne_zero_and_rational_member_twisted_of_finiteFamily_arch_deep.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_mem_rsLocalIntegral_ne_zero_and_rational_member_twisted_of_finiteFamily_arch_deep
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
    (hw₂b0 : w₂b ≠ 0)

    (hw₂blaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂b (UnramifiedWhittaker.unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂b g)
    (hw₂bK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p Φ.level, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂b (g * k) = w₂b g)

    (dMp : ℕ)
    (hπ₀levMp : ∃ W' ∈ gl3CyclicSubspace (mP ⟨p, hp⟩), W' ≠ 0 ∧
      ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ (p : HeightOneSpectrum (𝓞 ℚ)),
        (∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) i j -
            (1 : Matrix (Fin 3) (Fin 3) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) i j) ≤ WithZero.exp (-(dMp : ℤ))) →
        ∀ g : LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)),
          ((NumberField.TateGlobal.localChar χA (p : HeightOneSpectrum (𝓞 ℚ)) (Matrix.GeneralLinearGroup.det (g * k)) : ℂˣ) : ℂ)⁻¹ * W' (g * k) =
            ((NumberField.TateGlobal.localChar χA (p : HeightOneSpectrum (𝓞 ℚ)) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * W' g)
    (hkCMp : 6 * (bQ (p : HeightOneSpectrum (𝓞 ℚ)) + 3 * dMp + 3) + 7 ≤ kχ (p : HeightOneSpectrum (𝓞 ℚ)))

    (lamMp : ℂ)
    (hlamMIdp :
    ∀ b : ℕ,
            (∀ w ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ K (p : HeightOneSpectrum (𝓞 ℚ)),
          2 * (Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal * b) + 1 ≤
            LanglandsTunnell.TateLocal.conductorExponentAt K w (NumberField.TateGlobal.localChar μ w)) →
        ∀ (η : ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ →* ℂˣ) (cη : ℕ),
          LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) η cη → cη ≤ b →
          ∀ ηA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, LanglandsTunnell.Converse.IsAdmissibleTwist ℚ ηA →
            NumberField.TateGlobal.localChar ηA (p : HeightOneSpectrum (𝓞 ℚ)) = η →
            LanglandsTunnell.Converse.IsAdmissibleTwist K
              (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) →
            ∀ g : LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)),
              letI := LanglandsTunnell.TateLocal.localBorel ℚ (p : HeightOneSpectrum (𝓞 ℚ))
              ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
                IsLocalZeta30ConvergentAbove (p : HeightOneSpectrum (𝓞 ℚ)) (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)))))
                  (mP ⟨p, hp⟩) η g σ₀ ∧
                (∀ s : ℂ, σ₀ < s.re →
                  localZeta30 (p : HeightOneSpectrum (𝓞 ℚ)) (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ (p : HeightOneSpectrum (𝓞 ℚ))))) (mP ⟨p, hp⟩) η s g *
                    Q₂.eval ((Ideal.absNorm (p : HeightOneSpectrum (𝓞 ℚ)).asIdeal : ℂ) ^ (-s)) =
                  Q₁.eval ((Ideal.absNorm (p : HeightOneSpectrum (𝓞 ℚ)).asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm (p : HeightOneSpectrum (𝓞 ℚ)).asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
                IsLocalZeta31ConvergentAbove (p : HeightOneSpectrum (𝓞 ℚ)) (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ (p : HeightOneSpectrum (𝓞 ℚ))))) (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ (p : HeightOneSpectrum (𝓞 ℚ))) (dualWhittakerFn3 (mP ⟨p, hp⟩)) η⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
                (∀ s : ℂ, σ₁ < (1 - s).re →
                  localZetaDual31 (p : HeightOneSpectrum (𝓞 ℚ)) (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ (p : HeightOneSpectrum (𝓞 ℚ))))) (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)))
                    (mP ⟨p, hp⟩) η (1 - s) g * Q₂.eval ((Ideal.absNorm (p : HeightOneSpectrum (𝓞 ℚ)).asIdeal : ℂ) ^ (-s)) =
                  Q₁.eval ((Ideal.absNorm (p : HeightOneSpectrum (𝓞 ℚ)).asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm (p : HeightOneSpectrum (𝓞 ℚ)).asIdeal : ℂ) ^ ((n : ℂ) * s) *
                    (lamMp *
                      (∏ᶠ w ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ K (p : HeightOneSpectrum (𝓞 ℚ)),
                        ((NumberField.TateGlobal.localChar
                          (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w (-1) : ℂˣ) : ℂ)) *
                      (∏ᶠ w ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ K (p : HeightOneSpectrum (𝓞 ℚ)),
                        (LanglandsTunnell.TateLocal.stdRootNumberAt K w
                            (NumberField.TateGlobal.localChar
                              (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w) *
                          (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^
                            (LanglandsTunnell.Converse.pinnedExp K
                                (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w))))))

    (hβMp : ∀ b : ℕ, ((p : HeightOneSpectrum (𝓞 ℚ)).asIdeal ^ b ∣ Φ.level ∧ ¬ (p : HeightOneSpectrum (𝓞 ℚ)).asIdeal ^ (b + 1) ∣ Φ.level) →
      ∀ (ϖp : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletionIntegers ℚ)
        (hπp : algebraMap ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletionIntegers ℚ) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) ϖp ≠ 0),
        Valued.v (algebraMap ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletionIntegers ℚ) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) ϖp) = WithZero.exp (-1 : ℤ) →
      ∀ (g₃ : LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ))) (k₀ : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) (η : ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ →* ℂˣ)
      (c : ℕ),
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) η c → c ≤ b →
      letI := LanglandsTunnell.TateLocal.localBorel ℚ (p : HeightOneSpectrum (𝓞 ℚ))
      letI := localGLBorel ℚ (p : HeightOneSpectrum (𝓞 ℚ))
      haveI := borelSpace_localGLBorel ℚ (p : HeightOneSpectrum (𝓞 ℚ))
      ∀ (μ₂ : Measure (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ))) [μ₂.IsHaarMeasure],
        ∃ T : Finset (ℤ × ℤ), ∀ n : ℤ × ℤ, n ∉ T →
          (∫ u in {u : ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ | Valued.v (u : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) = 1},
              (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ (p : HeightOneSpectrum (𝓞 ℚ)) ((p : HeightOneSpectrum (𝓞 ℚ)).asIdeal ^ (b)) :
                    Subgroup (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ))) : Set (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ))),
                  (mP ⟨p, hp⟩) (iotaGL (UnramifiedWhittaker.scalarPi
                        (algebraMap ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletionIntegers ℚ) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) ϖp) hπp ^ n.2 *
                      diagUnitGL2 (Units.mk0 (algebraMap ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletionIntegers ℚ) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) ϖp) hπp
                        ^ n.1 * u) * (k₀ * k)) * g₃) ∂μ₂) * ((η u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)))))) = 0 ∧
          (∫ u in {u : ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ | Valued.v (u : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) = 1},
              (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ (p : HeightOneSpectrum (𝓞 ℚ)) ((p : HeightOneSpectrum (𝓞 ℚ)).asIdeal ^ (b)) :
                    Subgroup (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ))) : Set (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ))),
                  dualWhittakerFn3 (fun x => (mP ⟨p, hp⟩) (x * g₃)) (iotaGL (UnramifiedWhittaker.scalarPi
                        (algebraMap ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletionIntegers ℚ) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) ϖp) hπp ^ n.2 *
                      diagUnitGL2 (Units.mk0 (algebraMap ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletionIntegers ℚ) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) ϖp) hπp
                        ^ n.1 * u) * (k₀ * AutomorphicForm.transposeInvN (Fin 2) k))) ∂μ₂) * ((η u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)))))) = 0) :
      letI := localGLBorel ℚ p
      haveI := borelSpace_localGLBorel ℚ p
      ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
          (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
        ∃ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
          fun g : GL (Fin 2) (p.adicCompletion ℚ) => (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * w₂b g) (g * h)),
          ∃ W₃ ∈ gl3CyclicSubspace (mP ⟨p, hp⟩),

            (∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
              RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                    (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                      (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                    s (fun g => W₃ (iotaGL g)) w₂ ≠ 0) ∧

            ∃ (P₀ Pd₀ Q₀ Qd₀ : Polynomial ℂ) (m₀ md₀ : ℤ) (σ₂ σ₃ : ℝ), P₀ ≠ 0 ∧ Qd₀ ≠ 0 ∧
                (∀ s : ℂ, σ₂ < s.re →
                  RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                      (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                      s (fun g => W₃ (iotaGL g)) w₂ * Q₀.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                    (Ideal.absNorm p.asIdeal : ℂ) ^ ((m₀ : ℂ) * s) * P₀.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
                (∀ s : ℂ, σ₃ < s.re →
                  RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                      (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                      s (fun g => dualWhittakerFn3 W₃ (iotaGL g))
                      (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ ((localAt ℚ p (globalPoints (𝓞 ℚ) ℚ w₀)) * transposeInvN (Fin 2) g)) *
                      Qd₀.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                    (Ideal.absNorm p.asIdeal : ℂ) ^ ((md₀ : ℂ) * s) * Pd₀.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) := by sorry
