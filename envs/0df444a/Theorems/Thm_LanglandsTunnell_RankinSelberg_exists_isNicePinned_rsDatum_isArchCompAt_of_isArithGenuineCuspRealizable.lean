-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_isNicePinned_rsDatum_isArchCompAt_of_isArithGenuineCuspRealizable
-- name    : LanglandsTunnell.RankinSelberg.exists_isNicePinned_rsDatum_isArchCompAt_of_isArithGenuineCuspRealizable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/ab2749dc-3486-59a1-9f76-eed08eba765e
-- title:
--   Pinned niceness of Rankin–Selberg L-data over a cubic field
-- statement:
--   Let $K$ be a number field with $[K:\mathbb{Q}]=3$, with $\mathcal{O}_K$ an integral $\mathcal{O}_{\mathbb{Q}}$-algebra, and let $\Phi$ be a Hecke eigensystem over $\mathbb{Q}$ with complex coefficients, i.e. a nonzero level ideal together with functions $p\mapsto \Phi.a\,p$, $p\mapsto \Phi.b\,p$ on the primes of $\mathcal{O}_{\mathbb{Q}}$. Assume: the renormalised system (same $a$, with $b$ divided by $\mathrm{cNorm}$) admits a genuine smooth cuspidal realization at the general production pins of $\mathbb{Q}$; a finite set $SQ_0$ of primes with $\|\Phi.b\,p\|=1$ for $p\notin SQ_0$; $\sum_p \|\Phi.a\,p\|\,N(p)^{-\sigma}$ summable for every real $\sigma>1$. Let $Tq$ be a finite set of primes of $\mathbb{Q}$ and let $\omega$ be a continuous unitary character of the idele units of $K$ trivial on principal ideles which, at every prime $\mathfrak{P}$ of $K$ whose prime below is outside $Tq$, is unramified and satisfies $\omega(\text{uniformizer idele at }\mathfrak{P})=\Phi.b(p)^{f(\mathfrak{P}/p)}$, the formal base change coefficient. Then there are a finite set $SQ\supseteq SQ_0$ with $\|\Phi.b\,p\|=1$ off $SQ$, the finite set $SK$ of primes of $K$ lying over $SQ$, real archimedean parameters $\mathrm{archR}_w$ at real places, complex archimedean parameters $\mathrm{archC}_w$ at complex places, characters $\epsilon_v$ of $(K_v)^\times$ for all primes $v$ (continuous for $v\in SK$), and functions $A,A^{d}:(SK\to\mathbb{Z})\to\mathbb{C}$, such that: every prime of $K$ over $Tq$ lies in $SK$; at a real place with $\mathrm{archR}_w=\mathrm{principal}(u_1,a_1,u_2,a_2)$ one has $a_1-a_2\neq p+1$ in $\mathbb{Z}/2$ whenever $u_1-u_2=p$ for a nonzero integer $p$; at a complex place neither $2(u_1-u_2)=\pm(p+q)$ with $k_1-k_2=\pm(p-q)$ occurs for integers $p,q\geq 1$; the archimedean component of $\omega$ at each real (resp. complex) place is $x\mapsto \|x\|^{\mathrm{mult}_w\cdot u}(x/\|x\|)^{a}$ with $u$ the central exponent and $a$ the central sign (resp. central twist) of the parameter there; $A$ and $A^{d}$ are bounded, vanish at all multi-indices not dominating some $n_0$, and $A\neq 0$; and for every continuous unitary idele class character $\mu$ of $K$ with $\mathrm{localChar}\,\mu\,v\cdot\epsilon_v=1$ on the valuation-one units at each $v\in SK$, and every archimedean data $(u_{\mathbb{R}},a_{\mathbb{R}},u_{\mathbb{C}},k_{\mathbb{C}})$ describing the archimedean components of $\mu$ in the same sense, the predicate `IsNicePinned` holds for the degree-six Rankin–Selberg $L$-datum $\mathrm{rsDatum}$ over the primes outside $SQ$, formed from $\Phi.a$, $\Phi.b$ and the unramified values of $\mu$ at primes of $K$ (zero at ramified ones), with gamma multisets the twists of $\mathrm{archR},\mathrm{archC}$ by those data and their duals: namely the datum is well formed, its Euler products converge with nonvanishing $L$-functions for $\mathrm{Re}\,s>1$, the conductor $\mathrm{finiteConductor}\,K\,\mu\,SK$ is positive, and there are entire functions $\Lambda,\Lambda^{d}$, bounded on vertical strips, equal on $\mathrm{Re}\,s>1$ to the products of the $S$-part series $\mathrm{sPart}\,K\,SK\,A\,\mu$, resp. $\mathrm{sPartDual}\,K\,SK\,A^{d}\,\mu$, with the corresponding archimedean factor and $L$-function, and satisfying $\Lambda(s)=\varepsilon\,N^{1/2-s}\Lambda^{d}(1-s)$ with $\varepsilon$ the pinned root number of the formal base change of $\Phi$ and $N$ that conductor.
--
--   This is the uniform niceness hypothesis required by the converse theorem for $\mathrm{GL}_2$ over a cubic field $K$: analytic continuation, boundedness in vertical strips and a functional equation, with root number and conductor pinned to the local constants, for the whole family of Rankin–Selberg $L$-functions of the eigensystem $\Phi$ twisted by admissible idele class characters $\mu$ of $K$ whose ramification at the places of $SK$ is prescribed by $\epsilon$. It feeds the construction of the twisted $L$-data of the formal base change of $\Phi$ along the route to the Langlands–Tunnell theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_isNicePinned_rsDatum_isArchCompAt_of_isArithGenuineCuspRealizable.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.Converse NumberField.TateGlobal
open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.exists_isNicePinned_rsDatum_isArchCompAt_of_isArithGenuineCuspRealizable
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ)
    (hΦ : AutomorphicForm.IsArithGenuineCuspRealizable ℚ
      (AutomorphicForm.productionPinsGeneral ℚ) Φ)
    (SQ₀ : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
    (hb : ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), p ∉ SQ₀ → ‖Φ.b p‖ = 1)
    (ha : ∀ σ : ℝ, 1 < σ →
      Summable fun p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) =>
        ‖Φ.a p‖ * (Ideal.absNorm p.asIdeal : ℝ) ^ (-σ))
    (Tq : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hω : IsAdmissibleTwist K ω)
    (hωT : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∉ Tq →
      IsUnramifiedCharAt ω 𝔓 ∧
        ((ω (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) = (formalBaseChange ℚ K Φ).b 𝔓) :
    ∃ (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))), SQ₀ ⊆ SQ ∧
    ∃ (SK : Finset (HeightOneSpectrum (𝓞 K))),
    (∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓 ∈ SK ↔ 𝔓.under (𝓞 ℚ) ∈ SQ) ∧
    (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ‖Φ.b p‖ = 1) ∧
    ∃
      (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
      (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
      (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
      (A Ad : (↥SK → ℤ) → ℂ),
      (∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∈ Tq → 𝔓 ∈ SK) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ →
          ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2)) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsComplex) (p q : ℕ), 1 ≤ p → 1 ≤ q →
        ¬ ((2 * ((archC w hw).u₁ - (archC w hw).u₂) = ((p + q : ℕ) : ℂ) ∧
              (archC w hw).k₁ - (archC w hw).k₂ = (p : ℤ) - q) ∨
            (2 * ((archC w hw).u₁ - (archC w hw).u₂) = -((p + q : ℕ) : ℂ) ∧
              (archC w hw).k₁ - (archC w hw).k₂ = (q : ℤ) - p))) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsReal),
        IsArchCompAt K ω w (archR w hw).centralExponent ((archR w hw).centralSign.val : ℤ)) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsComplex),
        IsArchCompAt K ω w (archC w hw).centralExponent (archC w hw).centralTwist) ∧
      (∀ v ∈ SK, Continuous ⇑(epsS v)) ∧
      (∃ C : ℝ, ∀ n : ↥SK → ℤ, ‖A n‖ ≤ C ∧ ‖Ad n‖ ≤ C) ∧
      (∃ n₀ : ↥SK → ℤ, ∀ n : ↥SK → ℤ, (∃ v, n v < n₀ v) → A n = 0 ∧ Ad n = 0) ∧
      (A ≠ 0) ∧
      (∀ μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ, IsAdmissibleTwist K μ →
        (∀ v ∈ SK, ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 →
          localChar μ v u * epsS v u = 1) →
        ∀ (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ)
          (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
          (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ)
          (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ),
          (∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ)) →
          (∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw)) →
          IsNicePinned
            (rsDatum ℚ SQ Φ.a Φ.b
              (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
              (twistedGammaR K archR uR aR) (twistedGammaC K archR archC uR aR uC kC)
              (twistedGammaR K (fun w hw => (archR w hw).dual) (fun w hw => -uR w hw) aR)
              (twistedGammaC K (fun w hw => (archR w hw).dual) (fun w hw => (archC w hw).dual)
                (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw)))
            (sPart K SK A μ) (sPartDual K SK Ad μ)
            (pinnedRootNumber K (formalBaseChange ℚ K Φ) μ SK archR archC uR aR uC kC)
            (finiteConductor K μ SK)) := by sorry
