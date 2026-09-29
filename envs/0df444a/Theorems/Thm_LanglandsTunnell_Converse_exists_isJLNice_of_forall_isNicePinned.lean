-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_exists_isJLNice_of_forall_isNicePinned
-- name    : LanglandsTunnell.Converse.exists_isJLNice_of_forall_isNicePinned
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/98bffdc9-08c7-51d6-b346-c833f36a2963
-- title:
--   Nice pinned twisted L-data yield Jacquet–Langlands S-data
-- statement:
--   Let $K$ be a number field, $\Pi$ a Hecke eigensystem over $K$ with complex values (a non-zero level ideal and families $a_v,b_v$ indexed by the height-one primes of $\mathcal{O}_K$), $S$ a finite set of such primes, $archR$ and $archC$ assignments of a real, resp. complex, archimedean parameter to each real, resp. complex, place of $K$, and $(\varepsilon_v)_v$ a family of homomorphisms $(K_v)^\times\to\mathbb{C}^\times$, assumed continuous for $v\in S$. Let $A,\hat A\colon(\mathbb{Z}^S)\to\mathbb{C}$ be bounded by one common constant $C$ and both vanish at every $n$ with $n_v<n_{0,v}$ for some $v$, for a fixed $n_0$, and assume $A\neq 0$. The hypothesis is that for every homomorphism $\mu\colon(\mathbb{A}_K)^\times\to\mathbb{C}^\times$ which is an admissible twist (trivial on $K^\times$, continuous, of absolute value $1$) and satisfies $\mu_v(u)\varepsilon_v(u)=1$ for all $v\in S$ and all $u$ of valuation $1$, and for all archimedean data $u_w,a_w\in\mathbb{Z}/2$ at the real places and $u_w,k_w$ at the complex places realising the archimedean components of $\mu$ in the sense of `IsArchCompAt`, the $L$-datum `twistedDatum` of $\Pi\otimes\mu$ away from $S$, with the $S$-series `sPart` of $A$ and `sPartDual` of $\hat A$, the root number `pinnedRootNumber` and the conductor `finiteConductor`, is nice pinned: the datum is well formed and convergent, the conductor is positive, and there are entire $\Lambda,\Lambda^{\vee}$ bounded on vertical strips agreeing for $\operatorname{Re} s>1$ with the respective products of the $S$-series, archimedean factor and $L$-function, and satisfying $\Lambda(s)=\varepsilon N^{1/2-s}\Lambda^{\vee}(1-s)$. The conclusion is that for every admissible twist $\omega$ there exists $d\colon$ `JLData K S epsS ω` — levels $m_v\ge 1$ on which $\varepsilon_v$ and $\omega_v$ are trivial, an element of $K^\times$ with valuation $-m_v$ at each $v\in S$, and bounded functions $a,\hat a$ on $K^\times$ with the stated $S$-unit equivariance, support and non-vanishing properties — such that `IsJLNice K S epsS ω d Pi archR archC` holds, i.e. for some system $R$ of $S$-order representatives and all $\mu$ satisfying `IsJLTwist` and all compatible archimedean data, the twisted datum is well formed and convergent and its completed series, formed from $d$, continue to entire functions bounded on strips and satisfy the functional equation with root number `pinnedRootNumber` and conductor `finiteConductor`.
--
--   This is the form in which the converse theorem for $\mathrm{GL}(2)$ with a finite set of exceptional places is used: bounded coefficient families on $\mathbb{Z}^S$ whose twisted completed series are all nice are converted into data at the places of $S$ (levels, an auxiliary element of $K^\times$, and coefficient functions on $K^\times$) satisfying the functional equations required there. It feeds the construction of arithmetic genuine cuspidal realisations from nice pinned data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_exists_isJLNice_of_forall_isNicePinned.lean

import Definitions.Def_LanglandsTunnell_JLData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsDedekindDomain NumberField AutomorphicForm NumberField.TateGlobal

theorem LanglandsTunnell.Converse.exists_isJLNice_of_forall_isNicePinned
    (K : Type) [Field K] [NumberField K]
    (Pi : HeckeEigensystem K ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (hepsS : ∀ v ∈ S, Continuous ⇑(epsS v))
    (A Ad : (↥S → ℤ) → ℂ)
    (hbd : ∃ C : ℝ, ∀ n : ↥S → ℤ, ‖A n‖ ≤ C ∧ ‖Ad n‖ ≤ C)
    (hsupp : ∃ n₀ : ↥S → ℤ, ∀ n : ↥S → ℤ, (∃ v, n v < n₀ v) → A n = 0 ∧ Ad n = 0)
    (hA0 : A ≠ 0)
    (hnice : ∀ μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ, IsAdmissibleTwist K μ →
      (∀ v ∈ S, ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 →
        localChar μ v u * epsS v u = 1) →
      ∀ (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ)
        (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
        (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ)
        (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ),
        (∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ)) →
        (∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw)) →
        IsNicePinned (twistedDatum K Pi S archR archC μ uR aR uC kC)
          (sPart K S A μ) (sPartDual K S Ad μ)
          (pinnedRootNumber K Pi μ S archR archC uR aR uC kC) (finiteConductor K μ S))
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hω : IsAdmissibleTwist K ω) :
    ∃ d : JLData K S epsS ω, IsJLNice K S epsS ω d Pi archR archC := by sorry
