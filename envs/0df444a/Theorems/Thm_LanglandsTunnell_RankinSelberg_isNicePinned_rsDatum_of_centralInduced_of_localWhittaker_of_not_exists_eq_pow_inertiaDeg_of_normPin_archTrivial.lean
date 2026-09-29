-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_isNicePinned_rsDatum_of_centralInduced_of_localWhittaker_of_not_exists_eq_pow_inertiaDeg_of_normPin_archTrivial
-- name    : LanglandsTunnell.RankinSelberg.isNicePinned_rsDatum_of_centralInduced_of_localWhittaker_of_not_exists_eq_pow_inertiaDeg_of_normPin_archTrivial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/07dafb07-4ae7-580a-a5dd-e632ef1630bd
-- title:
--   Niceness of the pinned Rankin–Selberg datum of a cubic twist
-- statement:
--   Throughout, $K$ is a number field with $\operatorname{finrank}_{\mathbb Q} K = 3$ (hypothesis `_hdeg`) whose ring of integers is an integral $\mathcal O_{\mathbb Q}$-algebra, and $\Phi$ is a Hecke eigensystem over $\mathbb Q$ with complex coefficients, i.e. a nonzero level ideal $\Phi.\mathrm{level}\subseteq\mathcal O_{\mathbb Q}$ together with coefficient functions $\Phi.a,\Phi.b$ on the height-one spectrum of $\mathcal O_{\mathbb Q}$.
--
--   **Finite sets, size and growth hypotheses.** A finite set $S_{\mathbb Q}$ of primes of $\mathbb Q$ is given, subject to `hSQ`: every $p$ with $\Phi.\mathrm{level}\subseteq p$ lies in $S_{\mathbb Q}$, and every prime $\mathfrak P$ of $K$ whose contraction to $\mathcal O_{\mathbb Q}$ lies outside $S_{\mathbb Q}$ has ramification index $1$. Further, `hb` asserts $\lVert\Phi.b\,p\rVert=1$ for $p\notin S_{\mathbb Q}$, and `ha` asserts that for every real $\sigma>1$ the series $\sum_p\lVert\Phi.a\,p\rVert\,N(p)^{-\sigma}$ converges. A finite set $S_K$ of primes of $K$ is given with `hSK`: $\mathfrak P\in S_K$ if and only if $\mathfrak P$ lies over a prime of $S_{\mathbb Q}$. Finally $P$ is a real archimedean parameter (either $\mathrm{principal}\,(u_1,a_1,u_2,a_2)$ with $u_i\in\mathbb C$, $a_i\in\mathbb Z/2$, or $\mathrm{discrete}\,(u_0,n)$ with $n\ge 1$), and $S$ is a finite set of primes of $\mathbb Q$ with $S\subseteq S_{\mathbb Q}$ (`hS`).
--
--   **The realisation-and-Whittaker hypothesis `hlink`.** It requires a smooth cusp realisation $R$ at the standard pins `productionPinsGeneral ℚ` of the eigensystem $\Phi.\mathrm{toRawCentral}$ (same level and same $a$, with $b$ rescaled by $(\mathrm{cNorm}\,v)^{-1}$), so $R$ carries a function $R.\mathrm{toFun}$ on $\mathrm{GL}_2$ of the adeles which is nonzero somewhere, a central character $R.\mathrm{centralChar}$ on the pins' central subgroup, is a smooth cusp automorphic function for it, is invariant under the level subgroup at $\Phi.\mathrm{level}$, and is a Hecke and central eigenfunction off its exceptional set; $R.\mathrm{toFun}$ is moreover continuous. Together with $R$ there is a function $C$ on pairs (finite idele, adelic $\mathrm{GL}_2$ element) with $C\,1\,1\neq 0$, subject to $R.\mathrm{exceptionalSet}\subseteq S$ and to the following archimedean constraints: in the principal case $P=\mathrm{principal}\,(u_1,a_1,u_2,a_2)$ one has $|\operatorname{Re}(u_1-u_2)|<1$, and for every nonzero integer $p$ with $u_1-u_2=p$ one has $a_1-a_2\neq p+1$ in $\mathbb Z/2$; and at each real place the central character of $R$, read as a character of the full idele group through the identification of the group with its top subgroup, has archimedean component $x\mapsto\lVert x\rVert^{\,\mathrm{mult}(w)(P.\mathrm{centralExponent}+1)}(x/\lVert x\rVert)^{P.\mathrm{centralSign}}$ in the sense of `IsArchCompAt`.
--
--   The final clause of `hlink` demands, for every parity function $\mathrm{par}:\text{InfinitePlace }\mathbb Q\to\mathbb Z/2$, functions $\varphi$ on adelic $\mathrm{GL}_2$, $W_r$ on places times $\mathbb C$, and weights $k$ on places, such that: $\varphi$ is an isotypic cusp form at the standard pins for the central character $R.\mathrm{centralChar}$, level $\Phi.\mathrm{level}$ and exceptional set $S$ with eigensystem $\Phi$ (smooth cuspidal, continuous, invariant under the level subgroup, a Hecke coset eigenfunction with eigenvalue $\Phi.a\,v$ and a central eigenfunction with eigenvalue $\Phi.\mathrm{toRawCentral}.b\,v$ at every $v\notin S$); $\varphi\neq 0$; at every $p\in S_{\mathbb Q}$ the local Whittaker space of $\varphi$ at $p$ for the standard additive character `psiQ` is irreducible under right translation (any nonzero member generates it), admissible (for every open subgroup $U$ of $\mathrm{GL}_2$ over the completion at $p$ there is a finite set spanning all $U$-right-invariant members) and smooth (every member is right invariant under some open subgroup); $\varphi$ is a right convolution $\mathrm{rightConv}\,\varphi\,\alpha=\varphi$ for some factorizable test function $\alpha$; at each real place $w$ the function $\varphi$ transforms under the archimedean row-isometry subgroup by the weight character `archWeightCharAt hw (k w)`; in the principal case $(k\,w:\mathbb C)=\mathrm{signShift}(a_1+\mathrm{par}\,w)+\mathrm{signShift}(a_2+\mathrm{par}\,w)$ and in the discrete case $k\,w=n+1$; the Whittaker coefficient of $\varphi$ at $1$ factorises, namely for every idele unit $a$ and every $g$ in the finite adelic $\mathrm{GL}_2$ subgroup,
--   $$\mathcal W(\varphi)\bigl(\mathrm{diagOne}(a)\,g\bigr)=\Bigl(\prod_{w}W_r\,w\bigl(a_\infty\text{ at }w\bigr)\Bigr)\cdot C(a_{\mathrm{fin}})\,g;$$
--   in the principal case with $a_1=a_2$ and $\mathrm{par}\,w=a_1$ one has $W_r\,w(-t)=(-1)^{a_1}W_r\,w(t)$ for real $t$; in the discrete case $W_r\,w(t)=0$ for $t<0$; in the principal case with $a_1=a_2$ and $\mathrm{par}\,w=a_1+1$ there is $s_0$ such that for $\operatorname{Re}s>s_0$ the Mellin transform of $t\mapsto (W_r\,w(t)+(-1)^{a_1}W_r\,w(-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}\,(P.\mathrm{twist}\,0\,a_1).\mathrm{archFactor}(s)$; and for every $b\in\mathbb Z/2$ with $b=\mathrm{par}\,w$ or $b=\mathrm{par}\,w+P.\mathrm{centralSign}$ there is $s_0$ such that for $\operatorname{Re}s>s_0$ the same Mellin transform (with $b$ in place of $a_1$) converges and equals $(P.\mathrm{twist}\,0\,b).\mathrm{archFactor}(s)$.
--
--   **The character $\omega$ matching the base change.** A finite set $T_{\mathbb Q}$ of primes of $\mathbb Q$ is given, and a character $\omega$ of the idele units of $K$ with values in $\mathbb C^\times$ which is admissible (`hω`: trivial on principal ideles, continuous, unitary), such that (`hωT`) at every $\mathfrak P$ lying over a prime outside $T_{\mathbb Q}$ the character $\omega$ is unramified and $\omega(\varpi_{\mathfrak P})=(\mathrm{formalBaseChange}\,\mathbb Q\,K\,\Phi).b\,\mathfrak P=(\Phi.b\,p)^{f(\mathfrak P|p)}$; every $\mathfrak P$ over a prime of $T_{\mathbb Q}$ lies in $S_K$ (`hE`); and the archimedean components of $\omega$ are pinned by $P$: at real places by the central exponent and central sign of $P$ (`hωR`), at complex places by the central exponent and central twist of the base change $P.\mathrm{baseChange}$ (`hωC`).
--
--   **The twisting character $\mu$.** $\mu$ is an admissible character of the idele units of $K$ (`hμ`) which is not of norm type (`hoff`): there is no admissible character $\eta$ of the ideles of $\mathbb Q$ with $\mu(\varpi_{\mathfrak P})=\eta(\varpi_p)^{f(\mathfrak P|p)}$ at all $\mathfrak P$ at which $\mu$ is unramified and $\eta$ is unramified at $p=\mathfrak P\cap\mathcal O_{\mathbb Q}$. The depth hypothesis `hdepth` requires, for every $w\in S_K$,
--   $$4\bigl(\operatorname{ord}_w(\Phi.\mathrm{level}\cdot\mathcal O_K)+n(\psi_w)+1\bigr)\le a(\mu_w),$$
--   where $\operatorname{ord}_w$ is the fractional-ideal count at $w$ of the pushforward of the level, $n(\psi_w)$ the level of the local standard additive character, and $a(\mu_w)$ the conductor exponent of the local component of $\mu$.
--
--   **The auxiliary character $\chi_A$ and the conductor floor.** $\chi_A$ is an admissible character of the ideles of $\mathbb Q$ (`hχA`), unramified outside $S_{\mathbb Q}$ (`hχoff`), with archimedean components trivial at the real places, in the sense of exponent $0$ and sign $0$ (`hχinf`), and with conductor exponents $k_\chi(p)$ at the places $p\in S_{\mathbb Q}$ (`hkχ`). A function $c_0$ on primes of $\mathbb Q$ bounds the conductor exponents of the descent-twisted character: for $p\in S_{\mathbb Q}$ and $w$ in the fibre of $p$ in $K$ there is $c\le c_0(p)$ which is the conductor exponent at $w$ of the local component of $\mu\cdot\bigl(\chi_A\circ\mathrm{idelicNorm}\bigr)^{-1}$, the norm being that of the genuine base change from $\mathbb Q$ to $K$ (`hν`). A function $b_{\mathbb Q}$ records the exact exponent of $p$ in the level, i.e. $p^{b_{\mathbb Q}(p)}\mid\Phi.\mathrm{level}$ and $p^{b_{\mathbb Q}(p)+1}\nmid\Phi.\mathrm{level}$ for $p\in S_{\mathbb Q}$ (`hbQ`). The floor hypothesis `hkfloor` requires, for every $p\in S_{\mathbb Q}$,
--   $$6\Bigl(b_{\mathbb Q}(p)+3\Bigl(2\Bigl(\textstyle\sum_{w\mid p}f_w\bigl(e_w\bigl(2(52+3c_0(p))+n(\psi_w)+2\bigr)+c_0(p)+n(\psi_w)+1\bigr)+\bigl(52+3c_0(p)\bigr)\Bigr)\Bigr)+3\Bigr)+7\ \le\ k_\chi(p),$$
--   the sum being the finite sum over the prime fibre of $p$ in $K$, with $f_w$ the inertia degree and $e_w$ the ramification index.
--
--   **The induced character $\omega_{\mathbb Q}$ and the archimedean data of $\mu$.** $\omega_{\mathbb Q}$ is a character of the ideles of $\mathbb Q$ subject to the threefold hypothesis `hωQ`: it is admissible; at every prime $p$ which is not bad for $\mu$ (neither ramified in $K$ nor twist-ramified above) it is unramified with Euler coefficient $\mathrm{inducedE3}$ of the coefficient function of $\mu$ at $p$, that is minus the degree-$3$ coefficient of the induced Euler polynomial; and for every system of archimedean data $u_R,a_R$ at the real places and $u_C,k_C$ at the complex places of $K$ pinning the archimedean components of $\mu$, the archimedean component of $\omega_{\mathbb Q}$ at every real place of $\mathbb Q$ has exponent $\sum_{w\ \mathrm{real}}u_R(w)+\sum_{w\ \mathrm{cplx}}2u_C(w)$ and integer part $\sum_{w\ \mathrm{real}}a_R(w)+\sum_{w\ \mathrm{cplx}}(k_C(w)+1)$, the sums being finite sums. Finally such data $u_R,a_R,u_C,k_C$ are given together with `hcR` and `hcC`, asserting that they do pin the archimedean components of $\mu$ at the real and at the complex places.
--
--   **Conclusion.** Let $D$ be the Rankin–Selberg $L$-datum $\mathrm{rsDatum}\,\mathbb Q\,S_{\mathbb Q}\,\Phi.a\,\Phi.b\,c$ with the four twisted gamma multisets described below, where $c(\mathfrak P)=\mu(\varpi_{\mathfrak P})$ if $\mu$ is unramified at $\mathfrak P$ and $c(\mathfrak P)=0$ otherwise. Thus $D$ is indexed by the primes $p\notin S_{\mathbb Q}$, its norm is $N(p)$, its Euler factor is $\mathrm{rsEulerPoly}$ formed from $\Phi.a\,p$, $\Phi.b\,p$ and the induced coefficients $E_1,E_2,E_3$ of $c$ at $p$, its dual Euler factor the same polynomial formed from $\Phi.a\,p/\Phi.b\,p$, $(\Phi.b\,p)^{-1}$ and the induced coefficients of $\mathfrak P\mapsto c(\mathfrak P)^{-1}$, its abscissa is $1$, its centre $1/2$ and its degree $6$; its real gamma multiset is the sum over the real places $w$ of $K$ of the $\Gamma_{\mathbb R}$-shifts of $P$ twisted by $(u_R(w),a_R(w))$, its complex gamma multiset the sum of the $\Gamma_{\mathbb C}$-shifts of the same twists of $P$ over real places together with those of $P.\mathrm{baseChange}$ twisted by $(u_C(w),k_C(w))$ over the complex places, and the two dual multisets the corresponding sums formed from the duals $P^\vee$ and $(P.\mathrm{baseChange})^\vee$ with $u_R,u_C,k_C$ negated and $a_R$ unchanged.
--
--   The assertion is $\mathrm{IsNicePinned}\,D\,\Lambda_S\,\Lambda_S^{\vee}\,\varepsilon\,N$ for $\Lambda_S$ the constant function $1$,
--   $$\Lambda_S^{\vee}(t)=\prod_{w\in S_K}\epsilon\bigl((\omega\mu)_w\bigr)\,\epsilon(\mu_w)\,\Bigl(N(w)^{1/2-t}\Bigr)^{-\bigl(\mathrm{pinnedExp}(\omega\mu,w)+\mathrm{pinnedExp}(\mu,w)\bigr)},$$
--   where $\epsilon$ denotes the standard local root number at $w$ of the indicated local character at $s=1/2$ and $\mathrm{pinnedExp}(\nu,w)=a(\nu_w)+n(\psi_w)$; $\varepsilon$ the pinned root number $\mathrm{pinnedRootNumber}$ of the formal base change of $\Phi$, of $\mu$, of $S_K$ and of the archimedean data $(P,P.\mathrm{baseChange},u_R,a_R,u_C,k_C)$, that is the product of the archimedean root number with the finite root number; and $N$ the finite conductor $\mathrm{finiteConductor}\,K\,\mu\,S_K=\prod_v^{f}N(v)^{2\,\mathrm{pinnedExp}(\mu,v)}$, the factor being $1$ for $v\in S_K$.
--
--   Unfolding $\mathrm{IsNicePinned}$, the conclusion states: $D$ is well formed; $D$ converges; $0<N$; and there exist functions $\Lambda,\Lambda^{\vee}:\mathbb C\to\mathbb C$, both differentiable on all of $\mathbb C$ and both bounded on vertical strips, such that for $\operatorname{Re}s>1$ one has $\Lambda(s)=\Lambda_S(s)\,D.\mathrm{archFactor}(s)\,D.\mathrm{LFun}(s)$, for $\operatorname{Re}s>1$ one has $\Lambda^{\vee}(s)=\Lambda_S^{\vee}(s)\,D.\mathrm{archFactorDual}(s)\,D.\mathrm{LFunDual}(s)$, and for every $s\in\mathbb C$
--   $$\Lambda(s)=\varepsilon\,N^{\,1/2-s}\,\Lambda^{\vee}(1-s).$$
--
--   This is the analytic input — entirety, boundedness on vertical strips and the pinned functional equation with prescribed sign and conductor — for the $\mathrm{GL}_2\times\mathrm{GL}_3$ Rankin–Selberg $L$-function of a cusp form on $\mathrm{GL}_2/\mathbb Q$ against the automorphic induction of a non-norm-type idele class character of a cubic field, packaged exactly in the shape required by the niceness hypothesis of the converse theorem. It is used by the two existence statements [`LanglandsTunnell.RankinSelberg.exists_isNicePinned_rsDatum_archOfParam_isArchCompAt_of_whittaker_link_of_isArithGenuineCuspRealizable_of_localWhittaker`](thm.html#LanglandsTunnell.RankinSelberg.exists_isNicePinned_rsDatum_archOfParam_isArchCompAt_of_whittaker_link_of_isArithGenuineCuspRealizable_of_localWhittaker) and [`LanglandsTunnell.RankinSelberg.exists_isNicePinned_rsDatum_isArchCompAt_of_isArithGenuineCuspRealizable`](thm.html#LanglandsTunnell.RankinSelberg.exists_isNicePinned_rsDatum_isArchCompAt_of_isArithGenuineCuspRealizable) on the cubic base-change route to the Langlands–Tunnell theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_isNicePinned_rsDatum_of_centralInduced_of_localWhittaker_of_not_exists_eq_pow_inertiaDeg_of_normPin_archTrivial.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Mathlib.Analysis.MellinTransform
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell
open LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda
open scoped nonZeroDivisors

open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.isNicePinned_rsDatum_of_centralInduced_of_localWhittaker_of_not_exists_eq_pow_inertiaDeg_of_normPin_archTrivial
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
    (hlink : ∃ R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral,
      Continuous R.toFun ∧
      ∃ C : FiniteAdeleRing (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ → ℂ,
      R.exceptionalSet ⊆ S ∧
      C 1 1 ≠ 0 ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1) ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₂ →
          ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2)) ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
        IsArchCompAt ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) w
          (P.centralExponent + 1) (P.centralSign.val : ℤ)) ∧
      ∀ par : InfinitePlace ℚ → ZMod 2,
        ∃ (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (Wr : InfinitePlace ℚ → ℂ → ℂ) (k : InfinitePlace ℚ → ℤ),
          IsIsotypicCuspFormAt ℚ
              (productionPinsGeneral ℚ)
              R.centralChar Φ.level S Φ φ ∧
          φ ≠ 0 ∧

          (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ SQ →
            ((∀ W₀ ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                NumberField.StandardAddChar.psiQ p φ,
              W₀ ≠ 0 → ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                NumberField.StandardAddChar.psiQ p φ,
                W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
                  fun g : GL (Fin 2) (p.adicCompletion ℚ) => W₀ (g * h))) ∧
            (∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
              ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
                ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                  NumberField.StandardAddChar.psiQ p φ,
                  (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g) →
                    W ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))) ∧
            (∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                NumberField.StandardAddChar.psiQ p φ,
              ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
                ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g))) ∧
          (∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ) ∧
          (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
            HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k w)) φ) ∧
          (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
            P = RealArchParam.principal u₁ a₁ u₂ a₂ →
              (k w : ℂ) = signShift (a₁ + par w) + signShift (a₂ + par w)) ∧
          (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
            P = RealArchParam.discrete u₀ n hn → k w = (n : ℤ) + 1) ∧
          (∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g ∈ finiteAdelicGL2Subgroup ℚ →
              whittakerCoefficient ℚ
                  (productionPinsGeneral ℚ)
                  NumberField.StandardAddChar.psiQ φ 1 (diagOne a * g)
                = (∏ w : InfinitePlace ℚ, Wr w (extensionEmbedding w ((a : AdeleRing (𝓞 ℚ) ℚ).1 w)))
                    * C (a : AdeleRing (𝓞 ℚ) ℚ).2 g) ∧
          (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
            P = RealArchParam.principal u₁ a₁ u₂ a₁ → par w = a₁ →
              ∀ t : ℝ, Wr w (-t) = (-1 : ℂ) ^ a₁.val * Wr w t) ∧
          (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
            P = RealArchParam.discrete u₀ n hn → ∀ t : ℝ, t < 0 → Wr w t = 0) ∧
          (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
            P = RealArchParam.principal u₁ a₁ u₂ a₁ → par w = a₁ + 1 →
              ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
                MellinConvergent
                    (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ a₁.val * Wr w (-t)) / (t : ℂ)) s ∧
                  mellin (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ a₁.val * Wr w (-t)) / (t : ℂ)) s
                    = (2 * s + u₁ + u₂ - 1) / (4 * (Real.pi : ℂ))
                        * (P.twist 0 a₁).archFactor s) ∧
          (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (b : ZMod 2),
            (b = par w ∨ b = par w + P.centralSign) →
              ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
                MellinConvergent
                    (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ b.val * Wr w (-t)) / (t : ℂ)) s ∧
                  mellin (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ b.val * Wr w (-t)) / (t : ℂ)) s
                    = (P.twist 0 b).archFactor s))
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
    (hdepth : ∀ w : ↥SK,
      4 * (FractionalIdeal.count K w.1
            ((Φ.level.map (algebraMap (𝓞 ℚ) (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) +
          LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w.1) + 1) ≤
        LanglandsTunnell.TateLocal.conductorExponentAt K w.1 (localChar μ w.1))
    (ωQ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hωQ : IsAdmissibleTwist ℚ ωQ ∧
      (∀ p : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ p →
        IsUnramifiedCharAt ωQ p ∧ eulerCoeff ℚ ωQ p = inducedE3 ℚ (inducedCoeff K μ) p) ∧
      ∀ (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
        (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ),
        (∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ)) →
        (∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw)) →
        ∀ v : InfinitePlace ℚ, v.IsReal →
          IsArchCompAt ℚ ωQ v
            ((∑ᶠ (w) (hw : w.IsReal), uR w hw) + (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw))
            ((∑ᶠ (w) (hw : w.IsReal), ((aR w hw).val : ℤ)) + (∑ᶠ (w) (hw : w.IsComplex), (kC w hw + 1))))
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ)
    (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ)
    (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (hcR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (hcC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw)) :
    IsNicePinned
      (rsDatum ℚ SQ Φ.a Φ.b
        (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
        (twistedGammaR K (archOfParamR K P) uR aR)
        (twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC)
        (twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR)
        (twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual)
          (fun w hw => (archOfParamC K P w hw).dual)
          (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw)))
      (fun _ => 1)
      (fun t : ℂ => ∏ w : ↥SK,
    LanglandsTunnell.TateLocal.stdRootNumberAt K w.1 (NumberField.TateGlobal.localChar (ω * μ) w.1) *
      LanglandsTunnell.TateLocal.stdRootNumberAt K w.1 (NumberField.TateGlobal.localChar μ w.1) *
      (((Ideal.absNorm w.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - t)) ^
        (-(LanglandsTunnell.Converse.pinnedExp K (ω * μ) w.1 + LanglandsTunnell.Converse.pinnedExp K μ w.1)))
      (pinnedRootNumber K (formalBaseChange ℚ K Φ) μ SK (archOfParamR K P) (archOfParamC K P)
        uR aR uC kC)
      (finiteConductor K μ SK) := by sorry
