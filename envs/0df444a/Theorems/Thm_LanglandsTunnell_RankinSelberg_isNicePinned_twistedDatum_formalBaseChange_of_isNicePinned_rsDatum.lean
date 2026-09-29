-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_isNicePinned_twistedDatum_formalBaseChange_of_isNicePinned_rsDatum
-- name    : LanglandsTunnell.RankinSelberg.isNicePinned_twistedDatum_formalBaseChange_of_isNicePinned_rsDatum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/a4a79868-dce5-5fbc-848b-9f001ae02320
-- title:
--   Pinned niceness passes from Rankin–Selberg datum to twisted base change
-- statement:
--   Let $K$ be a number field with $[K:\mathbb{Q}]=3$, equipped with an $\mathcal{O}_{\mathbb{Q}}$-algebra structure on $\mathcal{O}_K$ that is integral; let $\Phi$ be a Hecke eigensystem over $\mathbb{Q}$ with complex coefficients (a nonzero level ideal together with coefficient functions $\Phi.a,\Phi.b$ on the primes of $\mathbb{Q}$). Let $S_{\mathbb{Q}}$ be a finite set of primes of $\mathbb{Q}$ and $T$ a finite set of primes of $K$ such that $\mathfrak{P}\in T$ exactly when the prime of $\mathbb{Q}$ under $\mathfrak{P}$ lies in $S_{\mathbb{Q}}$; assume $\|\Phi.b(p)\|=1$ for $p\notin S_{\mathbb{Q}}$, and that $p\mapsto\|\Phi.a(p)\|\,(\mathrm{N}p)^{-\sigma}$ is summable for every real $\sigma>1$. Fix archimedean parameters $\mathrm{arch}_{\mathbb{R}}$ at the real places and $\mathrm{arch}_{\mathbb{C}}$ at the complex places of $K$, a homomorphism $\mu$ from the idele units of $K$ to $\mathbb{C}^{\times}$ which is trivial on principal ideles, continuous and unitary, twist data $u_{\mathbb{R}},a_{\mathbb{R}}$ at the real places and $u_{\mathbb{C}},k_{\mathbb{C}}$ at the complex places, functions $\Lambda_S,\Lambda_S^{\vee}:\mathbb{C}\to\mathbb{C}$, $\varepsilon\in\mathbb{C}$ and $N\in\mathbb{R}$. Suppose the Rankin–Selberg $L$-datum `rsDatum` over $\mathbb{Q}$ indexed by the primes outside $S_{\mathbb{Q}}$ — Euler factor at $p$ the polynomial `rsEulerPoly` of $(\Phi.a(p),\Phi.b(p))$ against the induced local data of the function sending $\mathfrak{P}$ to $\mu(\varpi_{\mathfrak{P}})$ when $\mu$ is unramified at $\mathfrak{P}$ and to $0$ otherwise, dual factor the corresponding polynomial for $(\Phi.a(p)/\Phi.b(p),\Phi.b(p)^{-1})$ and the inverted values, gamma multisets the twisted $\Gamma_{\mathbb{R}}$- and $\Gamma_{\mathbb{C}}$-data of $(\mathrm{arch}_{\mathbb{R}},\mathrm{arch}_{\mathbb{C}})$ twisted by $(u_{\mathbb{R}},a_{\mathbb{R}},u_{\mathbb{C}},k_{\mathbb{C}})$ and their duals, abscissa $1$, centre $1/2$, degree $6$ — is nicely pinned by $(\Lambda_S,\Lambda_S^{\vee},\varepsilon,N)$, i.e. it is well formed, its Euler product converges, $N>0$, and there exist entire $\Lambda,\Lambda^{\vee}$ bounded on vertical strips with $\Lambda(s)=\Lambda_S(s)\cdot(\text{arch factor})(s)\cdot L(s)$ and $\Lambda^{\vee}(s)=\Lambda_S^{\vee}(s)\cdot(\text{dual arch factor})(s)\cdot L^{\vee}(s)$ for $\mathrm{Re}\,s>1$, and $\Lambda(s)=\varepsilon N^{1/2-s}\Lambda^{\vee}(1-s)$ for all $s$. Then the twisted $L$-datum `twistedDatum` over $K$ indexed by the primes outside $T$, built from the formal base change of $\Phi$ (level $\mathcal{O}_K$, coefficients $a_{\mathfrak{P}}=\mathrm{satakePow}$ of residue degree applied to $(\Phi.a(p),\Phi.b(p))$ and $b_{\mathfrak{P}}=\Phi.b(p)^{f}$ for $p$ the prime under $\mathfrak{P}$), with the same archimedean parameters, twist $\mu$ and twist data, degree $2$, is nicely pinned by the same $(\Lambda_S,\Lambda_S^{\vee},\varepsilon,N)$.
--
--   This is the transfer step in the converse-theorem route to the Langlands–Tunnell theorem: the analytic package (entirety, boundedness on strips, functional equation) established for the Rankin–Selberg convolution over $\mathbb{Q}$ against the local data induced from the cubic field $K$ is carried over to the twisted $L$-datum of the formal cubic base change over $K$, the two Euler products agreeing factor by factor above each unramified prime. It feeds the existence statements producing nicely pinned twisted $L$-data for the base change, which are the input to the converse theorem over $K$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_isNicePinned_twistedDatum_formalBaseChange_of_isNicePinned_rsDatum.lean

import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_AutomorphicForm_FormalBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm LanglandsTunnell.Converse NumberField.TateGlobal
open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.isNicePinned_twistedDatum_formalBaseChange_of_isNicePinned_rsDatum
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (Φ : HeckeEigensystem ℚ ℂ)
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hfib : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓 ∈ T ↔ 𝔓.under (𝓞 ℚ) ∈ SQ)
    (hb : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ‖Φ.b p‖ = 1)
    (ha : ∀ σ : ℝ, 1 < σ →
      Summable fun p : HeightOneSpectrum (𝓞 ℚ) => ‖Φ.a p‖ * (Ideal.absNorm p.asIdeal : ℝ) ^ (-σ))
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (ΛS ΛSd : ℂ → ℂ) (ε : ℂ) (N : ℝ)
    (hRS : IsNicePinned
      (rsDatum ℚ SQ Φ.a Φ.b
        (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
        (twistedGammaR K archR uR aR) (twistedGammaC K archR archC uR aR uC kC)
        (twistedGammaR K (fun w hw => (archR w hw).dual) (fun w hw => -uR w hw) aR)
        (twistedGammaC K (fun w hw => (archR w hw).dual) (fun w hw => (archC w hw).dual)
          (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw)))
      ΛS ΛSd ε N) :
    IsNicePinned (twistedDatum K (formalBaseChange ℚ K Φ) T archR archC μ uR aR uC kC) ΛS ΛSd ε N := by sorry
