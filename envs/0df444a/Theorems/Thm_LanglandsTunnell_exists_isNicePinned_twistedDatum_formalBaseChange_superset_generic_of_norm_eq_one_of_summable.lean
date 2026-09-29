-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_isNicePinned_twistedDatum_formalBaseChange_superset_generic_of_norm_eq_one_of_summable
-- name    : LanglandsTunnell.exists_isNicePinned_twistedDatum_formalBaseChange_superset_generic_of_norm_eq_one_of_summable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/730718f0-cde1-51ef-a9ad-5aeccf339bc6
-- title:
--   Niceness of generic twisted base-change data over a cubic field
-- statement:
--   Let $K$ be a number field of degree $3$ over $\mathbb{Q}$, with $\mathcal{O}_K$ an integral $\mathcal{O}_{\mathbb{Q}}$-algebra, and let $\Phi$ be a Hecke eigensystem over $\mathbb{Q}$ with complex coefficients (a level together with functions $p \mapsto \Phi.a\,p$, $p \mapsto \Phi.b\,p$ on the finite places) such that the eigensystem $\Phi$, with $\Phi.b$ rescaled by $(\mathrm{cNorm}\,v)^{-1}$, admits a genuine smooth cuspidal realisation at the general production pins of $\mathbb{Q}$. Assume a finite set $SQ_0$ with $\|\Phi.b\,p\| = 1$ for $p \notin SQ_0$, and $\sum_p \|\Phi.a\,p\|\,N(p)^{-\sigma} < \infty$ for every real $\sigma > 1$. Assume further a finite set $S_0$ and $\chi : \{\text{finite places of } \mathbb{Q}\} \to \mathbb{C}$ with $\chi_v^2 = 1$ off $S_0$, with $\chi_v = 1$ off $S_0$ exactly when no prime $\mathfrak{P}$ of $K$ above $v$ has inertia degree $2$, and such that there is no finite set outside which $\Phi.a\,v = \chi_v\,\Phi.a\,v$ and $\Phi.b\,v = \chi_v^2\,\Phi.b\,v$. Finally let $T_{\mathbb{Q}}$ be a finite set of finite places of $\mathbb{Q}$ and $\omega$ a continuous unitary idele class character of $K$ which at every $\mathfrak{P}$ not above $T_{\mathbb{Q}}$ is unramified and sends the idele with a uniformiser at $\mathfrak{P}$ to $(\mathrm{formalBaseChange}\ \mathbb{Q}\ K\ \Phi).b\,\mathfrak{P} = (\Phi.b\,(\mathfrak{P}\cap\mathbb{Q}))^{f(\mathfrak{P})}$. Then there exist a finite set $S$ of finite places of $K$, real and complex archimedean parameters $\mathrm{archR}$, $\mathrm{archC}$, local characters $\mathrm{epsS}_v$, and coefficient functions $A, A^{\vee} : (S \to \mathbb{Z}) \to \mathbb{C}$ such that: $S$ contains every prime of $K$ above $T_{\mathbb{Q}}$; for $v \notin S$ the base-changed coefficients satisfy $a_v^2 \neq b_v\,(N v + 2 + (N v)^{-1})$; each principal real parameter $(u_1,a_1,u_2,a_2)$ satisfies $a_1 - a_2 \neq p+1$ in $\mathbb{Z}/2$ whenever $u_1 - u_2 = p$ for a nonzero integer $p$; each complex parameter avoids $2(u_1-u_2) = \pm(p+q)$ together with $k_1 - k_2 = \pm(p-q)$ for integers $p,q \geq 1$; the archimedean components of $\omega$ at real, resp. complex, places are given by $|x|^{\mathrm{mult}\cdot u}(x/|x|)^a$ with $u$ the central exponent and $a$ the central sign, resp. central twist, of the corresponding parameter; the $\mathrm{epsS}_v$ are continuous for $v \in S$; $A$ and $A^{\vee}$ are uniformly bounded, vanish at every $n$ with some coordinate below a fixed $n_0$, and $A \neq 0$; and for every continuous unitary idele class character $\mu$ of $K$ whose local character at each $v \in S$ is inverse to $\mathrm{epsS}_v$ on units of valuation $1$, and every $(u_R,a_R,u_C,k_C)$ describing the archimedean components of $\mu$, the twisted $L$-datum of the formal base change (Euler factors $1 - \mu(\varpi_v)a_v X + \mu(\varpi_v)^2 b_v X^2$ at unramified $v \notin S$, and the dual ones, with the twisted gamma multisets, abscissa $1$, centre $1/2$, degree $2$) is nice pinned with $S$-parts $\mathrm{sPart}$, $\mathrm{sPartDual}$ formed from $A$, $A^{\vee}$, root number $\mathrm{pinnedRootNumber}$ and conductor $\mathrm{finiteConductor}$: the datum is well formed and convergent, the conductor is positive, and there are differentiable $\Lambda, \Lambda^{\vee}$ bounded on vertical strips agreeing on $\mathrm{Re}\,s > 1$ with the $S$-part times the archimedean factor times the $L$-function (respectively their duals) and satisfying $\Lambda(s) = \varepsilon\,N^{1/2-s}\Lambda^{\vee}(1-s)$.
--
--   This is the first of the two inputs needed for the $\mathrm{GL}(2)$ converse theorem over $K$ in the non-normal cubic transfer behind the Langlands–Tunnell theorem: it supplies, for a prescribed set of rational primes and a prescribed central character, a complete package of analytically nice pinned $L$-data for all admissible twists of the formal base change of $\Phi$ to $K$, together with the genericity inequality at places outside the exceptional set. It feeds the construction of a Hecke eigensystem over $K$ agreeing with the formal base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_isNicePinned_twistedDatum_formalBaseChange_superset_generic_of_norm_eq_one_of_summable.lean

import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume
open LanglandsTunnell.Converse NumberField.TateGlobal

theorem LanglandsTunnell.exists_isNicePinned_twistedDatum_formalBaseChange_superset_generic_of_norm_eq_one_of_summable
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
    (S₀ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (χ : HeightOneSpectrum (𝓞 ℚ) → ℂ)
    (_hχ2 : ∀ v ∉ S₀, χ v * χ v = 1)
    (_hlink : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S₀ →
      (χ v = 1 ↔ ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) = v →
        (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal ≠ 2))
    (_hnd : ¬ HeckeEigensystem.AgreesAwayFromFinite Φ (Φ.twist χ))
    (Tq : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hω : IsAdmissibleTwist K ω)
    (hωT : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∉ Tq →
      IsUnramifiedCharAt ω 𝔓 ∧
        ((ω (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) = (formalBaseChange ℚ K Φ).b 𝔓) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K)))
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (A Ad : (↥S → ℤ) → ℂ),
    (∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∈ Tq → 𝔓 ∈ S) ∧
    (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      (formalBaseChange ℚ K Φ).a v ^ 2 ≠
        (formalBaseChange ℚ K Φ).b v *
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) + 2 + ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)⁻¹)) ∧
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
    (∀ v ∈ S, Continuous ⇑(epsS v)) ∧
    (∃ C : ℝ, ∀ n : ↥S → ℤ, ‖A n‖ ≤ C ∧ ‖Ad n‖ ≤ C) ∧
    (∃ n₀ : ↥S → ℤ, ∀ n : ↥S → ℤ, (∃ v, n v < n₀ v) → A n = 0 ∧ Ad n = 0) ∧
    (A ≠ 0) ∧
    (∀ μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ, IsAdmissibleTwist K μ →
      (∀ v ∈ S, ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 →
        localChar μ v u * epsS v u = 1) →
      ∀ (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ)
        (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
        (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ)
        (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ),
        (∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ)) →
        (∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw)) →
        IsNicePinned (twistedDatum K (formalBaseChange ℚ K Φ) S archR archC μ uR aR uC kC)
          (sPart K S A μ) (sPartDual K S Ad μ)
          (pinnedRootNumber K (formalBaseChange ℚ K Φ) μ S archR archC uR aR uC kC)
          (finiteConductor K μ S)) := by sorry
