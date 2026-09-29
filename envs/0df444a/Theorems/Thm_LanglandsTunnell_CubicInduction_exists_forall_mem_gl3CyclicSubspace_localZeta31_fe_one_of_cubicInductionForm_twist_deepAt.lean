-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_mem_gl3CyclicSubspace_localZeta31_fe_one_of_cubicInductionForm_twist_deepAt
-- name    : LanglandsTunnell.CubicInduction.exists_forall_mem_gl3CyclicSubspace_localZeta31_fe_one_of_cubicInductionForm_twist_deepAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/d312ceaa-0cd1-582c-b88d-5bfda99e2a1c
-- title:
--   Local functional equation at one deeply twisted prime
-- statement:
--   Setting. $K$ is a number field whose ring of integers is an integral $\mathcal O_{\mathbb Q}$-algebra, of degree $3$ over $\mathbb Q$ (hypothesis `_hdeg`). The character $\nu \colon (\mathbb A_K)^\times \to \mathbb C^\times$ is an admissible twist of $K$ (`hνadm`): it is trivial on the image of $K^\times$, continuous, and all its values have modulus $1$. The hypothesis `hoff` states that $\nu$ is of no norm type in the following precise sense: there is no admissible twist $\eta$ of $\mathbb Q$ such that for every prime $\mathfrak P$ of $\mathcal O_K$ at which $\nu$ is unramified and whose trace $\mathfrak p = \mathfrak P \cap \mathcal O_{\mathbb Q}$ carries $\eta$ unramified, $\nu$ of the uniformiser idèle at $\mathfrak P$ equals $\eta$ of the uniformiser idèle at $\mathfrak p$ raised to the inertia degree $f(\mathfrak P/\mathfrak p)$.
--
--   The auxiliary data at one prime. $p$ is a prime of $\mathcal O_{\mathbb Q}$ and $\xi_{\mathbb A}$ an admissible twist of $\mathbb Q$ (`hξA`) which is unramified at every prime $v \neq p$ (`hξoff`) and whose archimedean component at the real place is trivial, in the sense that its archimedean local character is $x \mapsto |x|^{0}(x/|x|)^{0}$ (`hξinf`, the clause `IsArchCompAt ℚ ξA v 0 0`). Natural numbers $B, c_0$ are given with: the local component of $\xi_{\mathbb A}$ at $p$ has exact conductor exponent $B$, i.e. it is trivial on the units congruent to $1$ modulo the $B$-th power of the maximal ideal and nontrivial on each lower such group (`hξB`); for each prime $\mathfrak P$ of $K$ above $p$ the local component of $\nu$ has an exact conductor exponent $c \le c_0$ (`hνc`); and $c_0 + 12 \le B$ (`hB`).
--
--   Archimedean parameters of $\nu$. Families $uR(w) \in \mathbb C$, $aR(w) \in \mathbb Z/2$ at the real places of $K$ and $uC(w) \in \mathbb C$, $kC(w) \in \mathbb Z$ at the complex places, such that the archimedean local character of $\nu$ at a real place $w$ is $x \mapsto \|x\|^{\mathrm{mult}(w)\,uR(w)}(x/\|x\|)^{aR(w)}$ and at a complex place $x \mapsto \|x\|^{\mathrm{mult}(w)\,uC(w)}(x/\|x\|)^{kC(w)}$ (`hcR`, `hcC`).
--
--   Additive character. $\psi$ is an additive character of $\mathbb A_{\mathbb Q}$ which is trivial on $\mathbb Q$, continuous and nontrivial (`hψ`), each of whose local components has level $0$ (`hlev`), and with $\psi^{-1}$ the standard global character `psiQ` (`hψQ`).
--
--   The central character of the induced object. $\omega_3$ is a character of the idèles of $\mathbb Q$ subject to `hω₃` (three clauses): it is an admissible twist; at every prime $v$ which is not bad for $(K,\nu)$ — that is, no prime above $v$ ramifies and $\nu$ is unramified at all primes above $v$ — $\omega_3$ is unramified and its Euler coefficient equals $\mathrm{inducedE3}$ of the coefficient system $\mathfrak P \mapsto \nu(\varpi_{\mathfrak P})$ (minus the degree-$3$ coefficient of the induced Euler polynomial over the fibre); and, for arbitrary archimedean data $uR, aR, uC, kC$ of $\nu$ as above, the archimedean type of $\omega_3$ at the real place of $\mathbb Q$ is given by the exponent $\sum_{w \text{ real}} uR(w) + \sum_{w \text{ complex}} 2\,uC(w)$ and the integer $\sum_{w \text{ real}} aR(w) + \sum_{w \text{ complex}} (kC(w)+1)$, the sums being finsums over the infinite places of $K$.
--
--   Splitting and archimedean normalisations. $E$ is a monoid homomorphism from the units of the infinite adèles of $\mathbb Q$ to the idèles whose infinite part is the identity and whose finite part is $1$ (`hE`). A nonzero rational $a$ is given (`ha`) together with a unit $a_{\infty}$ of the infinite adèles representing it (`haInf`), the additive character $\psi_\infty(x) = \mathrm{psiArch}(a x)$ (`hpsiInf`), and the compatibility that the restriction of $\psi$ to the infinite component is $\psi_\infty$ (`hψinf`). The additive measure $\nu_{\mathrm{add}}$ on the infinite adèles is $|a|^{1/2}$ times the transport of Lebesgue measure along the identification with the mixed space (`hν_add`), and $\nu_{\mathrm{mul}}$ is a Haar measure on the units of the infinite adèles.
--
--   The archimedean Whittaker function. $W_{\mathrm{arch}} \colon \mathrm{GL}_3$ of the infinite adèles $\to \mathbb C$ satisfies the conjunction `hWarch` (grouped here): it is nonzero; $K$-finite, in the sense that the right translates by the orthogonal group lie in the span of a finite set of functions; continuous and gauge-bounded, there being $t$ such that for every $N$ some $C$ bounds $\|W_{\mathrm{arch}}(g_\infty)\|$ by $C$ divided by $(\prod_w \mathrm{archRoot}_1 \cdot \mathrm{archRoot}_2)^t (1+\mathrm{archRootSum})^N$; it is a $\psi_\infty$-Whittaker function, $W_{\mathrm{arch}}(u(x,y,z)g) = \psi_\infty(x+y)W_{\mathrm{arch}}(g)$ for upper unipotent $u(x,y,z)$; it transforms under the central scalar $z$ by $\omega_3(E z)$; for every admissible twist $\sigma$ of $\mathbb Q$ of real archimedean type $(t,e)$ and every $g_\infty$ there is a function $P$, differentiable on $\mathbb C$, with an abscissa above which the archimedean zeta integral $\mathrm{archZeta30}$ of $h \mapsto W_{\mathrm{arch}}(h g_\infty)$ against $\sigma \circ E$ converges and equals $P(s)$ times the archimedean factor of the Hecke datum of $K$, $\nu$ with parameters shifted by $(t,e)$, with $P$ of at most exponential growth in vertical strips, the product $P(s)\cdot(\text{archimedean factor})$ decaying faster than any power of $|\mathrm{Im}\,s|$ in strips, and a dual archimedean functional equation for $\mathrm{archZetaDual31}$ at $1-s$ whose constant is the product of the signs $\mathrm{signEpsilon}(aR(w)+e)$ over real places of $K$, the factors $i^{|kC(w)|}$ over complex places, $\prod_w \lambda_{\mathrm{arch}}(K,w)$, $\omega_3(E a_\infty)\cdot \sigma(E a_\infty)^3$ and $|a|^{3(s-1/2)}$, times $P(s)$ times the dual archimedean factor of the same Hecke datum at $1-s$; finally, some admissible $\sigma$ and some $s$ give $\mathrm{archZeta30}$ of $W_{\mathrm{arch}}$ nonzero.
--
--   The cubic induction form. $F$ is a `CubicInductionForm` for $K$, the production carrier pins over $\mathbb Q$ built from the class-representative Siegel set with parameters $(1/2,1,1/2,2)$, the levels $\mathrm{levelOne} \sqcap \mathrm{finiteAdelicGL2Subgroup}$, the Hecke generators and the adelic box, the character $\psi$ and the twist $\nu$: thus a cuspidal automorphic function on $\mathrm{GL}_3$ of the adèles of $\mathbb Q$ with its Whittaker function, local Whittaker functions, archimedean Whittaker function, central character and dual Whittaker function, satisfying the axioms of that structure. The further hypotheses on $F$ are: `hF0`, that $F.\mathrm{form} \neq 0$ and that at every prime $v$ unramified in $K$ whose local component of $\psi$ has level $0$ one has $F.\mathrm{whittakerLoc}\,v\,(1) = 1$ and the spherical torus values prescribed by the coefficients of $\nu$; continuity of $F.\mathrm{form}$, $F.\mathrm{whittaker}$ and $F.\mathrm{dualWhittaker}$ (`hFc`, `hFw`, `hFdw`); gauge majorisation of $F.\mathrm{whittaker}$ and $F.\mathrm{dualWhittaker}$ (`hFg`, `hFdg`); the identification $F.\mathrm{whittakerArch} = W_{\mathrm{arch}}$ (`hArchEq`); the essential-vector hypothesis `hEss`, that at every bad prime $v$ which is unramified in $K$ and at which the local component of $\psi$ is the inverse of the standard local character there is a nonzero $\psi_v$-Whittaker vector $W$ in the cyclic subspace generated by the right translates of $F.\mathrm{whittakerLoc}\,v$, invariant under right translation by the congruence subgroup $K_1$ of level $\mathrm{inducedLevelAt}\,K\,\nu\,v$, with $W(1)=1$ and the spherical torus values of the coefficients of $\nu$; the bad-place hypothesis `hBad`, that for every finite set $T$ of primes, at each bad $v \in T$ the function $F.\mathrm{whittakerLoc}\,v$ is right invariant under some open subgroup, and each nonzero member of its cyclic subspace generates $F.\mathrm{whittakerLoc}\,v$ back; and the admissibility hypothesis `hadm`, that at each bad prime $v$ and each open subgroup $U_v$ there is a finite set of functions whose span contains every $U_v$-right-invariant member of the cyclic subspace of $F.\mathrm{whittakerLoc}\,v$.
--
--   Conclusion. There exist $\varepsilon \in \mathbb C$ and $\ell \in \mathbb N$ with $\varepsilon \neq 0$ and the following four assertions.
--
--   First, $\ell$ equals the finsum over the primes $\mathfrak P$ of $K$ above $p$ of $f(\mathfrak P/p)$ times the pinned exponent of $\nu \cdot (\xi_{\mathbb A} \circ N)$ at $\mathfrak P$, where $N$ is the idelic norm of the genuine base change from $\mathbb Q$ to $K$ and the pinned exponent at $\mathfrak P$ is the conductor exponent of the local component plus the level of the standard local additive character of $K_{\mathfrak P}$.
--
--   Second, $B \le \ell$.
--
--   Third, $\ell \le 3B + \sum_{\mathfrak P \mid p} f(\mathfrak P/p)\cdot$ (level of the standard local additive character of $K_{\mathfrak P}$), the sum again a finsum over the fibre.
--
--   Fourth, write $q = \#(\mathcal O_{\mathbb Q}/p)$ for the absolute norm of $p$ and let $\mu$ be the multiplicative measure on the units of the completion at $p$ obtained by restricting the self-dual additive Haar measure away from $0$, dividing by the modulus and pulling back along the inclusion of the units, and $\nu_p$ the self-dual additive Haar measure at $p$, the completion being equipped with its Borel $\sigma$-algebra. Then for every $W$ in the cyclic subspace generated under right translation by the twisted local Whittaker function $g \mapsto \xi_{\mathbb A,p}(\det g)\cdot F.\mathrm{whittakerLoc}\,p\,(g)$, and for every $g$ in $\mathrm{GL}_3$ of the completion at $p$, there are $P \colon \mathbb C \to \mathbb C$ and reals $\sigma_0, \sigma_1$ such that:
--
--   (a) $P$ is a rational function of $q^{-s}$ up to a monomial: there are polynomials $Q, R \in \mathbb C[X]$ with $R \neq 0$ and an $m \in \mathbb N$ with $P(s)\,R(q^{-s}) = Q(q^{-s})\,q^{m s}$ for all $s \in \mathbb C$;
--
--   (b) the zeta integrand $a \mapsto W(\iota(\mathrm{diag}(a,1))g)\,|a|^{s-1}$ (with trivial multiplicative character) is $\mu$-integrable for $\mathrm{Re}\,s > \sigma_0$;
--
--   (c) for $\mathrm{Re}\,s > \sigma_0$, $\mathrm{localZeta30}$ at $p$ of $W$ with trivial character, base point $g$, equals the inverse of the evaluation of the constant polynomial $1$ at $q^{-s}$ times $P(s)$, so that the local $L$-factor occurring is trivial;
--
--   (d) the corresponding two-variable integrand for $\mathrm{localZeta31}$ of $\mathrm{dualWhittakerFn3}(W)$ with trivial character at the base point $w' \cdot {}^{t}g^{-1}$ converges above $\sigma_1$, against the product of $\mu$ and $\nu_p$;
--
--   (e) for all $s$ with $\mathrm{Re}(1-s) > \sigma_1$, the dual local zeta integral $\mathrm{localZetaDual31}$ at $p$ of $W$ with trivial character, at $1-s$ and base point $g$, equals the inverse of the evaluation of the constant polynomial $1$ at $q^{-(1-s)}$ times $\bigl(\varepsilon\, q^{\,\ell(1/2-s)}\bigr)\,P(s)$.
--
--   Thus both local $L$-factors are trivial and the local $\gamma$-factor is the monomial $\varepsilon\,q^{\ell(1/2-s)}$, with the same $\varepsilon$ and $\ell$ for all $W$ in the cyclic subspace and all $g$.
--
--   This identifies the local functional-equation data of the $\mathrm{GL}_3 \times \mathrm{GL}_1$ zeta integrals at the single prime $p$ where an auxiliary idèle class character is taken to be highly ramified: the local $L$-factors degenerate to $1$ and the $\gamma$-factor becomes a monomial in $q^{-s}$ with exponent read off from the conductor and different exponents in the fibre above $p$. It feeds the converse-theorem input for the cubic induction, being used in the assembly of the entire, strip-bounded completed $L$-function of the Rankin–Selberg datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_forall_mem_gl3CyclicSubspace_localZeta31_fe_one_of_cubicInductionForm_twist_deepAt.lean

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

theorem LanglandsTunnell.CubicInduction.exists_forall_mem_gl3CyclicSubspace_localZeta31_fe_one_of_cubicInductionForm_twist_deepAt
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hνadm : LanglandsTunnell.Converse.IsAdmissibleTwist K ν)
    (hoff : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt ν 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((ν (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))

    (p : HeightOneSpectrum (𝓞 ℚ))
    (ξA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hξA : LanglandsTunnell.Converse.IsAdmissibleTwist ℚ ξA)
    (hξoff : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ p → IsUnramifiedCharAt ξA v)
    (hξinf : ∀ v : InfinitePlace ℚ, v.IsReal → LanglandsTunnell.Converse.IsArchCompAt ℚ ξA v 0 0)
    (B c₀ : ℕ)
    (hξB : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p (NumberField.TateGlobal.localChar ξA p) B)
    (hνc : ∀ w ∈ primeFibre ℚ K p, ∃ c : ℕ, c ≤ c₀ ∧
      LanglandsTunnell.TateLocal.HasConductorExponentAt K w (NumberField.TateGlobal.localChar ν w) c)
    (hB : c₀ + 12 ≤ B)
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
    ∃ (ε : ℂ) (ℓ : ℕ), ε ≠ 0 ∧

      (ℓ : ℤ) = ∑ᶠ 𝔓 ∈ primeFibre ℚ K p, (p.asIdeal.inertiaDeg' 𝔓.asIdeal : ℤ) *
        LanglandsTunnell.Converse.pinnedExp K (ν * ξA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) 𝔓 ∧
      B ≤ ℓ ∧
      (ℓ : ℤ) ≤ 3 * (B : ℤ) + ∑ᶠ 𝔓 ∈ primeFibre ℚ K p, (p.asIdeal.inertiaDeg' 𝔓.asIdeal : ℤ) *
        LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K 𝔓) ∧
      ∀ W ∈ gl3CyclicSubspace
          (fun g : LocalGL3 p => ((NumberField.TateGlobal.localChar ξA p (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            F.whittakerLoc p g),
      ∀ g : LocalGL3 p,
        (letI := localBorel ℚ p
         ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
          (∃ (Q R : Polynomial ℂ) (m : ℕ), R ≠ 0 ∧ ∀ s : ℂ,
            P s * R.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
          IsLocalZeta30ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) W 1 g σ₀ ∧
          (∀ s : ℂ, σ₀ < s.re →
            localZeta30 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) W 1 s g =
              ((1 : Polynomial ℂ).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))⁻¹ * P s) ∧
          IsLocalZeta31ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
            (selfDualHaarAt ℚ p) (dualWhittakerFn3 W) 1 (weylPrime3 * transposeInv3 g) σ₁ ∧
          ∀ s : ℂ, σ₁ < (1 - s).re →
            localZetaDual31 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p)
                W 1 (1 - s) g =
              ((1 : Polynomial ℂ).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-(1 - s))))⁻¹ *
                ((ε * (Ideal.absNorm p.asIdeal : ℂ) ^ ((ℓ : ℂ) * (1 / 2 - s))) * P s)) := by sorry
