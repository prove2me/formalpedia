-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_exists_jlData_isJLNice_of_forall_isNicePinned
-- name    : LanglandsTunnell.Converse.exists_jlData_isJLNice_of_forall_isNicePinned
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/3d1ff385-3202-5120-a38c-73af21164d76
-- title:
--   Jacquet–Langlands data from pinned niceness of twisted L-data
-- statement:
--   Let $K$ be a number field, $\Pi$ a Hecke eigensystem over $K$ with complex coefficients (a nonzero level ideal together with families $a_v, b_v$ indexed by the finite places), $S$ a finite set of finite places of $K$, and $(\mathrm{archR}_w)_w$, $(\mathrm{archC}_w)_w$ assignments of a real, resp. complex, archimedean parameter to each real, resp. complex, place. Let $\varepsilon_v \colon (K_v)^\times \to \mathbb{C}^\times$ be a homomorphism for each finite $v$, continuous for $v \in S$, and let $A, A^\vee \colon (S \to \mathbb{Z}) \to \mathbb{C}$ admit a common bound $C$ with $\|A(n)\|, \|A^\vee(n)\| \le C$ and a common floor $n_0$, in the sense that $A(n) = A^\vee(n) = 0$ whenever $n_v < n_0(v)$ for some $v$, with $A \neq 0$. Assume the following niceness hypothesis: for every homomorphism $\mu$ on the idele units that is an admissible twist (trivial on the image of $K^\times$, continuous, and of absolute value $1$ everywhere) and satisfies $\mathrm{localChar}\,\mu_v(u)\,\varepsilon_v(u) = 1$ for all $v \in S$ and all $u$ of valuation $1$, and for all archimedean data $u_w^{\mathbb{R}} \in \mathbb{C}$, $a_w^{\mathbb{R}} \in \mathbb{Z}/2$, $u_w^{\mathbb{C}} \in \mathbb{C}$, $k_w^{\mathbb{C}} \in \mathbb{Z}$ describing the local components of $\mu$ at the infinite places in the sense of `IsArchCompAt` (with the lift of $a_w^{\mathbb{R}}$ to $\mathbb{Z}$ used at real places), the $L$-datum `twistedDatum K Pi S archR archC μ uR aR uC kC` is `IsNicePinned` relative to the $S$-parts $\sum_n A(n)\prod_{v \in S}(\mu_v(\varpi_v) q_v^{1/2-s})^{n_v}$ and $\sum_n A^\vee(n)\prod_{v\in S}(\mu_v(\varpi_v)^{-1} q_v^{1/2-s})^{n_v}$, the pinned root number, and the finite conductor $\prod_{v \notin S} q_v^{2\,\mathrm{pinnedExp}}$; that is, the datum is well formed and convergent, the conductor is positive, and there are entire functions $\Lambda, \Lambda^\vee$, bounded on vertical strips, agreeing with the product of the respective $S$-part, archimedean factor and $L$-function in the half-plane $\mathrm{Re}\,s > 1$, and satisfying $\Lambda(s) = \varepsilon N^{1/2-s}\Lambda^\vee(1-s)$. Let finally $\omega$ be an admissible twist. Then for every $m_{\mathrm{low}} \colon S \to \mathbb{N}$ there is a datum $J$ of type `JLData K S epsS ω` — levels $m_v \ge 1$ at which $\varepsilon_v$ and $\mathrm{localChar}\,\omega_v$ are trivial on the units congruent to $1$ modulo $m_v$, an element of $K^\times$ whose valuation at each $v \in S$ is $\exp(-m_v)$, and bounded coefficient functions $a, a^\vee$ on $K^\times$ transforming under multiplication by $S$-units by $\prod_{v\in S}\varepsilon_v$, resp. by $\prod_{v\in S}\mathrm{localChar}\,\omega_v \cdot \varepsilon_v^{-1}$, vanishing when the local valuation at some $v \in S$ exceeds the level of the local additive character $\mathrm{psiLocal}$, with $a$ not identically zero — such that $m_{\mathrm{low}}(v) \le m_v$ for all $v \in S$ and $J$ satisfies `IsJLNice K S epsS ω J Pi archR archC`: there is a system of representatives of $S$-orders for which, for every $\mu$ satisfying the predicate `IsJLTwist` and every compatible archimedean tuple, the twisted datum is well formed and convergent and, for some $\sigma_0$, the associated $S$-sums converge for $\mathrm{Re}\,s > \sigma_0$ and are interpolated by entire functions $\Lambda, \Lambda^\vee$ bounded on vertical strips which satisfy the functional equation with the factor $\mathrm{sFactor}$, the pinned root number and the finite conductor.
--
--   This is the bridge from the converse-theorem input (pinned niceness of all the twisted $L$-data attached to $\Pi$ with prescribed $S$-components) to the Hecke-theoretic data of Jacquet–Langlands type on which the construction of an automorphic form is based, in the style of the Hecke theory of Jacquet and Langlands over a global field. It is used in the proof that the archimedean parameters occurring in the relevant Whittaker fibre are the expected ones.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_exists_jlData_isJLNice_of_forall_isNicePinned.lean

import Definitions.Def_LanglandsTunnell_JLData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm NumberField.TateGlobal

theorem LanglandsTunnell.Converse.exists_jlData_isJLNice_of_forall_isNicePinned
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
    ∀ mlow : ↥S → ℕ, ∃ J : JLData K S epsS ω,
      (∀ v : ↥S, mlow v ≤ J.m v) ∧ IsJLNice K S epsS ω J Pi archR archC := by sorry
