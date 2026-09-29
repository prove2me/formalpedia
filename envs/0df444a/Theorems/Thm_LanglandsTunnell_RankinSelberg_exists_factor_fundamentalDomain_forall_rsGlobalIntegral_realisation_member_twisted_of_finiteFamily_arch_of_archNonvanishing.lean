-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_factor_fundamentalDomain_forall_rsGlobalIntegral_realisation_member_twisted_of_finiteFamily_arch_of_archNonvanishing
-- name    : LanglandsTunnell.RankinSelberg.exists_factor_fundamentalDomain_forall_rsGlobalIntegral_realisation_member_twisted_of_finiteFamily_arch_of_archNonvanishing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/0744ed6c-b7e8-535a-875c-01b5ca8a51c4
-- title:
--   Global realisation of local Rankin–Selberg pairs at p
-- statement:
--   Throughout, $K$ is a number field equipped with an integral $\mathcal O_{\mathbb Q}$-algebra structure on $\mathcal O_K$, and `_hdeg` records $[K:\mathbb Q]=3$.
--
--   **The $\mathrm{GL}_2$ eigensystem and its exceptional sets.** $\Phi$ is a Hecke eigensystem over $\mathbb Q$ with complex values (a nonzero level ideal together with families $\Phi.a$, $\Phi.b$ indexed by the finite places). $SQ$ is a finite set of finite places of $\mathbb Q$ such that (`hSQ`) every $p$ with $\Phi.\mathrm{level}\le p$ lies in $SQ$ and every prime $\mathfrak P$ of $K$ whose trace to $\mathbb Q$ avoids $SQ$ has ramification index $1$; `hb` requires $\|\Phi.b\,p\|=1$ off $SQ$, and `ha` requires $\sum_p\|\Phi.a\,p\|\,N(p)^{-\sigma}$ to converge for every $\sigma>1$. $SK$ is the finite set of primes of $K$ lying over $SQ$ (`hSK`), and $S\subseteq SQ$.
--
--   **The archimedean parameter.** $P$ is a real archimedean parameter, either principal, given by $(u_1,a_1,u_2,a_2)$ with $a_i\in\mathbb Z/2$, or discrete, given by $(u_0,n)$ with $n\ge 1$. In the principal case `hP1` requires $|\mathrm{Re}(u_1-u_2)|<1$ and `hP2` requires $a_1-a_2\neq p+1 \bmod 2$ whenever $u_1-u_2=p$ for a nonzero integer $p$.
--
--   **The cuspidal realisation.** $R$ is a smooth cuspidal realisation of the renormalised eigensystem $\Phi.\mathrm{toRawCentral}$ (the one with $b$ replaced by $N(v)^{-1}\Phi.b\,v$) for the production pin data on $\mathbb Q$, with $R.\mathrm{toFun}$ continuous (`hRc`) and exceptional set contained in $S$ (`hRS`); $C_{\mathrm{fin}}$ is a function of a finite adele and an adelic $\mathrm{GL}_2$ element; `hRcen` says that at each real place the central character of $R$ has archimedean component of exponent $P.\mathrm{centralExponent}+1$ and sign $P.\mathrm{centralSign}$, in the sense of `IsArchCompAt`.
--
--   **The finite family of forms.** For each parity $\mathrm{par}:\mathrm{InfinitePlace}\,\mathbb Q\to\mathbb Z/2$ there are a form $\varphi_{\mathrm{par}}$ on $\mathrm{GL}_2(\mathbb A_{\mathbb Q})$, archimedean Whittaker functions $W_{\mathrm r}(\mathrm{par},w,\cdot)$ and integer weights $k_w(\mathrm{par},w)$, subject to: `hiso`, that $\varphi_{\mathrm{par}}$ is an isotypic cusp form for the production pins with central character $R.\mathrm{centralChar}$, level $\Phi.\mathrm{level}$ and Hecke and central eigenvalues given by $\Phi$ off $S$; `hφne`, that $\varphi_{\mathrm{par}}\neq0$; `hφKf`, that $\varphi_{\mathrm{par}}$ is right-convolution invariant under some factorizable test function; `hφarch`, that at each real place $\varphi_{\mathrm{par}}$ satisfies `HasArchCharacterAt₀` for the weight character `archWeightCharAt` of exponent $k_w(\mathrm{par},w)$; `hkw1` and `hkw2`, which prescribe $k_w$ as $\mathrm{signShift}(a_1+\mathrm{par}\,w)+\mathrm{signShift}(a_2+\mathrm{par}\,w)$ in the principal case and as $n+1$ in the discrete case; `hφW`, that for every idele unit $a$ and every $g$ in the finite adelic $\mathrm{GL}_2$ subgroup the Whittaker coefficient of $\varphi_{\mathrm{par}}$ at $1$, evaluated at $\mathrm{diag}(a,1)g$, factors as $\prod_w W_{\mathrm r}(\mathrm{par},w,a_w)$ times $C_{\mathrm{fin}}$ of the finite part of $a$ at $g$; and the four archimedean clauses `hWr1`–`hWr4`: the parity relation $W_{\mathrm r}(\mathrm{par},w,-t)=(-1)^{a_1}W_{\mathrm r}(\mathrm{par},w,t)$ when $P$ is principal with equal signs $a_1$ and $\mathrm{par}\,w=a_1$; vanishing on $t<0$ in the discrete case; and, on suitable right half-planes, Mellin convergence of $t\mapsto (W_{\mathrm r}(\mathrm{par},w,t)+(-1)^{b}W_{\mathrm r}(\mathrm{par},w,-t))/t$ with Mellin transform equal to $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean factor of $P.\mathrm{twist}\,0\,a_1$ when $\mathrm{par}\,w=a_1+1$ (`hWr3`), and equal to the archimedean factor of $P.\mathrm{twist}\,0\,b$ for $b=\mathrm{par}\,w$ or $b=\mathrm{par}\,w+P.\mathrm{centralSign}$ (`hWr4`).
--
--   **The Hecke character over $K$ matching the base change.** $Tq$ is a finite set of finite places of $\mathbb Q$ and $\omega$ an admissible twist of $K$ (an idele class character that is continuous and unitary); `hωT` says that at every prime $\mathfrak P$ of $K$ not above $Tq$ the character $\omega$ is unramified and its value at the uniformiser idele is $\Phi.b$ of the underlying place raised to the inertia degree, i.e. the formal base change of $\Phi$; `hE` says the primes above $Tq$ lie in $SK$; `hωR` and `hωC` prescribe the archimedean components of $\omega$ at real and complex places through $P$ and its complexification.
--
--   **The non-base-change twist and its conductor bookkeeping.** $\mu$ is an admissible twist of $K$ with: `hoff`, the assertion that no admissible twist $\eta$ of $\mathbb Q$ matches $\mu$ in the sense that at all primes where both are unramified the value of $\mu$ at the uniformiser idele equals that of $\eta$ raised to the inertia degree; `hdepth`, the depth bound $4\big(\mathrm{ord}_w(\Phi.\mathrm{level}\,\mathcal O_K)+\ell_w+1\big)\le \mathrm{cond}_w(\mu_w)$ for $w\in SK$, where $\ell_w$ is the level of the standard local additive character; and `hcR`, `hcC`, which present the archimedean components of $\mu$ at real places as $(u_{\mathrm R}(w),a_{\mathrm R}(w))$ and at complex places as $(u_{\mathrm C}(w),k_{\mathrm C}(w))$. Further, $\chi_{\mathbb A}$ is an admissible twist of $\mathbb Q$ (`hχA`), unramified off $SQ$ (`hχoff`), with conductor exponent $k_\chi(p)$ at each $p\in SQ$ (`hkχ`) and trivial archimedean data at real places (`hχinf`); $c_0$ bounds (`hν`) the conductor exponents of $\mu\cdot(\chi_{\mathbb A}\circ\mathrm{Nm})^{-1}$ at the primes of $K$ above each $p\in SQ$; $b_{\mathbb Q}(p)$ is the exact exponent of $p$ in $\Phi.\mathrm{level}$ (`hbQ`); and `hkfloor` requires
--   $$6\Big(b_{\mathbb Q}(p)+3\Big(2\Big(\sum_{w\mid p}f_w\big(e_w(2(52+3c_0(p))+\ell_w+2)+c_0(p)+\ell_w+1\big)+(52+3c_0(p))\Big)\Big)+3\Big)+7\le k_\chi(p)$$
--   for $p\in SQ$, with $f_w,e_w$ the inertia degree and ramification index. Finally $\nu$ is an admissible twist of $K$ with $\mu=\nu\cdot(\chi_{\mathbb A}\circ\mathrm{Nm})$ (`hμν`).
--
--   **The additive character and the cubic induction form.** $\psi$ is a global additive character of $\mathbb A_{\mathbb Q}$ (`hψ`) of local level $0$ everywhere (`hlev`) with $\psi^{-1}$ the standard character $\psi_{\mathbb Q}$ (`hψQ`). $F$ is a cubic induction form for $K$, the production pin data, $\psi$ and $\nu$, carrying its global form, its global and local and archimedean Whittaker functions and its dual Whittaker function. It satisfies: `hF0`, $F.\mathrm{form}\neq0$ and, at places $v$ unramified in $K$ with $\psi_v$ of level $0$, the normalisation $F.\mathrm{whittakerLoc}\,v\,1=1$ together with the prescribed spherical torus values for the induced coefficients of $\nu$; `hFc`, `hFw`, `hFdw`, continuity of the form and of the two Whittaker functions; `hFg`, `hFdg`, gauge majorisation of both Whittaker functions; and `hBad`, which for every finite set $T$ provides, at each bad place of $T$ for $\nu$, an open subgroup under which $F.\mathrm{whittakerLoc}\,v$ is right invariant and the cyclicity statement that $F.\mathrm{whittakerLoc}\,v$ lies in the cyclic subspace generated by any nonzero member of its own cyclic subspace.
--
--   **Places, uniformisers and the auxiliary element.** $S'\supseteq SQ$ is finite (`hSS'`) with no place outside $S'$ bad for $\mu$ (`hgood`); $\varpi_p$ are local integers that, off $SQ$, are nonzero (`hπ`) of valuation $\exp(-1)$ (`hϖ`). The element $h_{\mu f}$ of the finite adelic $\mathrm{GL}_2$ subgroup is prescribed (`hhμf`) as the product over $p\in S'\setminus SQ$ of the place-$p$ embeddings of the scalar matrices $\mathrm{diag}(\varpi_p,\varpi_p)$ raised to $-\,\mathrm{inducedLevelAt}\,K\,\mu\,p$.
--
--   **The local $\mathrm{GL}_3$ vectors.** For each $p\in SQ$, $m_p$ is a function on $\mathrm{GL}_3(\mathbb Q_p)$ lying in the cyclic subspace generated by $g\mapsto \chi_{\mathbb A,p}(\det g)\,F.\mathrm{whittakerLoc}\,p\,g$ (`hmPmem`), normalised by $m_p(1)=1$ (`hmP1`), admissible in the sense that for each open subgroup the invariant vectors of the cyclic subspace of $m_p$ lie in the span of a finite set (`hW₃admM`), and irreducible in the sense that $m_p$ lies in the cyclic subspace of any nonzero member of its cyclic subspace (`hW₃irrM`).
--
--   **The split Whittaker factors and the local $\mathrm{GL}_2$ data.** $W_A$ and $W_f$ are archimedean and finite factors with $\mathrm{whittakerCoefficient}$ of $\varphi_{\mathrm{par}}$ at $1$ equal to $W_A(\mathrm{par})$ of the real component times $W_f(\mathrm{par})$ of the finite component (`hWAf`), with $W_f(\mathrm{par},g)=C_{\mathrm{fin}}(1,g)$ (`hWfC`) and $W_f(\mathrm{par},1)\neq0$ (`hWf1`); `hV` asserts, for each $p\in SQ$, that the local Whittaker space of $\varphi_{\mathrm{par}}$ at $p$ is irreducible (every nonzero member generates it by right translates), admissible (finite spanning sets for the vectors invariant under a given open subgroup) and smooth (every member is right invariant under some open subgroup). $w_0\in\mathrm{GL}_2(\mathbb Q)$ is the matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ (`hw₀`), and $W_{fd}$ is defined (`hWfd`) by $W_{fd}(\mathrm{par},g_f)=\|\det g_f\|_{\mathbb A}\,W_f(\mathrm{par})$ of the finite factor of $w_0\cdot{}^t g_f^{-1}$.
--
--   **The distinguished local vector and the archimedean non-vanishing hypothesis.** A parity $\mathrm{par}$, a place $p\in SQ$ and a member $w_{2b}$ of the local Whittaker space of $\varphi_{\mathrm{par}}$ at $p$ are fixed. The hypothesis `hΨA` requires that for every Haar measure $\mu_{NA}$ on the unipotent subgroup of $\mathrm{GL}_2(\mathbb R)$ there exist $h_A\in\mathrm{GL}_2(\mathbb R)$, $h_{A3}\in\mathrm{GL}_3(\mathbb A_{\mathbb Q,\infty})$ and $\sigma\in\mathbb R$ such that the archimedean Rankin–Selberg integral, taken with [`RSCarrier.archMeasure`](def/LanglandsTunnell_RSCarrierSplit.html#L11) and $\mu_{NA}$, of the pair $M\mapsto |\det M|^{-1/2}W_A(\mathrm{par},Mh_A)$ and $M\mapsto F.\mathrm{whittakerArch}$ of the image of $M$ under the real embedding followed by $\iota$, multiplied by $h_{A3}$, is holomorphic on $\{\mathrm{Re}\,s>\sigma\}$ and nonzero at some $s$ with $\mathrm{Re}\,s>\sigma$.
--
--   **Conclusion.** For every Haar measure $\mu_2$ on $\mathrm{GL}_2(\mathbb Q_p)$ (with its Borel structure) and every Haar measure $\mu_{N_2}$ on the range of the unipotent homomorphism $\mathbb Q_p\to\mathrm{GL}_2(\mathbb Q_p)$, there exist functions $M,M^\vee:\mathbb C\to\mathbb C$ and a set $D\subseteq\mathrm{GL}_2(\mathbb A_{\mathbb Q})$ such that:
--
--   1.
--
--   $D$ is a fundamental domain for the action of the image of $\mathrm{GL}_2(\mathbb Q)$ in $\mathrm{GL}_2(\mathbb A_{\mathbb Q})$ with respect to the adelic Haar measure on $\mathrm{GL}_2$;
--
--   2.
--
--   $M$ vanishes identically on no right half-plane: for every $\sigma'$ there is $s$ with $\mathrm{Re}\,s>\sigma'$ and $M(s)\neq0$;
--
--   3.
--
--   for every $w_2$ in the $\mathbb C$-span of the right translates of $g\mapsto |\det g|_p^{-1/2}w_{2b}(g)$ and every $W_3$ in the cyclic subspace generated by $m_p$, there exist $\varphi:\mathrm{GL}_2(\mathbb A_{\mathbb Q})\to\mathbb C$ and $\Theta:\mathrm{GL}_3(\mathbb A_{\mathbb Q})\to\mathbb C$ with the following four properties, where $Z(s;\varphi,\Theta;D)=\int_D\varphi(g)\,\Theta(\iota g)\,\|\det g\|^{s-1/2}$ denotes the global Rankin–Selberg integral:
--
--   (i) $s\mapsto Z(s;\varphi,\Theta;D)$ is entire;
--
--   (ii) for all $s\in\mathbb C$,
--    $$Z\big(1+s;\varphi\circ({}^t(\cdot)^{-1}),\Theta^\vee;{}^t D^{-1}\big)=Z(-s;\varphi,\Theta;D),$$
--    where ${}^tD^{-1}$ is the preimage of $D$ under $g\mapsto{}^tg^{-1}$ and $\Theta^\vee(g)=\Theta({}^tg^{-1})$ on $\mathrm{GL}_3$;
--
--   (iii) there is $\sigma$ such that for $\mathrm{Re}\,s>\sigma$ the global integral over $D$ equals $M(s)$ times the local Rankin–Selberg integral $\Psi_p$, namely the integral of $W_3(\iota_{\mathrm{GL}}g)\,w_2(g)\,|\det g|_p^{\,s-1/2}$ over $\mathrm{GL}_2(\mathbb Q_p)$ taken with respect to $\mu_2$ weighted by the quotient density of the unipotent subgroup for $\mu_{N_2}$;
--
--   (iv) there is $\sigma'$ such that for $\mathrm{Re}\,s>\sigma'$ the dual global integral $Z(1+s;\varphi\circ({}^t(\cdot)^{-1}),\Theta^\vee;{}^tD^{-1})$ equals $M^\vee(s)$ times the local integral of the same shape formed from the dual local vectors $g\mapsto W_3(\mathrm{longWeyl}_3\cdot{}^t(\iota_{\mathrm{GL}}g)^{-1})$ and $g\mapsto |\det g|_p\,w_2\big((w_0)_p\cdot{}^tg^{-1}\big)$, where $(w_0)_p$ is the $p$-component of $w_0$.
--
--   The functions $M$, $M^\vee$ and the domain $D$ are chosen before $w_2$ and $W_3$, hence are independent of the pair realised.
--
--   This is the global step of $\mathrm{GL}_3\times\mathrm{GL}_2$ Rankin–Selberg theory in the form needed for the converse theorem: every admissible local pair at the chosen place $p$ is realised by a global pair whose Rankin–Selberg integral is entire, satisfies the global functional equation $s\leftrightarrow -s$, and unfolds on right half-planes to the local integral times a factor independent of the pair. It is the input to the construction of the local gamma factor at $p$ ([`LanglandsTunnell.RankinSelberg.exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi`](thm.html#LanglandsTunnell.RankinSelberg.exists_rational_gamma_rsLocalIntegral_member_twisted_of_finiteFamily_arch_deep_archPsi)) in the Langlands–Tunnell part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_factor_fundamentalDomain_forall_rsGlobalIntegral_realisation_member_twisted_of_finiteFamily_arch_of_archNonvanishing.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_factor_fundamentalDomain_forall_rsGlobalIntegral_realisation_member_twisted_of_finiteFamily_arch_of_archNonvanishing
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
      letI := localGLBorel ℚ p
      haveI := borelSpace_localGLBorel ℚ p
      ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
          (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
        ∃ (M Md : ℂ → ℂ) (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)),
          IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D
              (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) ∧

          (∀ σ' : ℝ, ∃ s : ℂ, σ' < s.re ∧ M s ≠ 0) ∧

          ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
          fun g : GL (Fin 2) (p.adicCompletion ℚ) => (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * w₂b g) (g * h)),
            ∀ W₃ ∈ gl3CyclicSubspace (mP ⟨p, hp⟩),
              ∃ (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (Θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
                Differentiable ℂ (fun s : ℂ => rsGlobalIntegral D s φ Θ) ∧
                (∀ s : ℂ, rsGlobalIntegral (transposeInvN (Fin 2) ⁻¹' D) (1 + s)
                    (fun g => φ (transposeInvN (Fin 2) g)) (dualForm Θ) = rsGlobalIntegral D (-s) φ Θ) ∧
                (∃ σ : ℝ, ∀ s : ℂ, σ < s.re → rsGlobalIntegral D s φ Θ = M s *
                  RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                    (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                      (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                    s (fun g => W₃ (iotaGL g)) w₂) ∧
                (∃ σ' : ℝ, ∀ s : ℂ, σ' < s.re →
                  rsGlobalIntegral (transposeInvN (Fin 2) ⁻¹' D) (1 + s)
                      (fun g => φ (transposeInvN (Fin 2) g)) (dualForm Θ) = Md s *
                  RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                    (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                      (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                    s (fun g => dualWhittakerFn3 W₃ (iotaGL g))
                    (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                      ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
                        w₂ ((localAt ℚ p (globalPoints (𝓞 ℚ) ℚ w₀)) * transposeInvN (Fin 2) g))) := by sorry
