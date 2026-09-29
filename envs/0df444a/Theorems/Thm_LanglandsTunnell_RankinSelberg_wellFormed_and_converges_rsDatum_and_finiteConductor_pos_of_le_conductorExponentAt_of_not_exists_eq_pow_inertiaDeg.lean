-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_wellFormed_and_converges_rsDatum_and_finiteConductor_pos_of_le_conductorExponentAt_of_not_exists_eq_pow_inertiaDeg
-- name    : LanglandsTunnell.RankinSelberg.wellFormed_and_converges_rsDatum_and_finiteConductor_pos_of_le_conductorExponentAt_of_not_exists_eq_pow_inertiaDeg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/f19c358e-1cc5-5cdb-a712-bfda242a1c1b
-- title:
--   Well-formedness, convergence and positive conductor for a twisted Rankin–Selberg datum
-- statement:
--   Throughout, $K$ is a number field whose degree over $\mathbb{Q}$ is $3$ (hypothesis `_hdeg`), with $\mathcal{O}_K$ an integral $\mathcal{O}_{\mathbb{Q}}$-algebra, and $\Phi$ is a Hecke eigensystem over $\mathbb{Q}$ with complex values: a nonzero ideal $\Phi.\mathrm{level}$ of $\mathcal{O}_{\mathbb{Q}}$ together with families $a_p=\Phi.a\,p$ and $b_p=\Phi.b\,p$ indexed by the height-one primes $p$ of $\mathcal{O}_{\mathbb{Q}}$.
--
--   **Finite data and Hecke bounds.** A finite set $S_{\mathbb{Q}}$ of primes of $\mathcal{O}_{\mathbb{Q}}$ is given, subject to `hSQ`: every $p$ with $\Phi.\mathrm{level}\le p$ lies in $S_{\mathbb{Q}}$, and every prime $\mathfrak{P}$ of $\mathcal{O}_K$ whose prime below lies outside $S_{\mathbb{Q}}$ has `Ideal.ramificationIdx'` equal to $1$. Further, `hb`: $\lVert b_p\rVert=1$ for $p\notin S_{\mathbb{Q}}$; and `ha`: for every real $\sigma>1$ the family $p\mapsto \lVert a_p\rVert\,\mathrm{N}(p)^{-\sigma}$ is summable, $\mathrm{N}$ denoting `Ideal.absNorm`. A finite set $S_K$ of primes of $\mathcal{O}_K$ is given with `hSK`: $\mathfrak{P}\in S_K$ if and only if the prime of $\mathcal{O}_{\mathbb{Q}}$ below $\mathfrak{P}$ lies in $S_{\mathbb{Q}}$. Finally $P$ is a real archimedean parameter (either `principal` $u_1,a_1,u_2,a_2$ with $a_i\in\mathbb{Z}/2$, or `discrete` $u_0,n$ with $1\le n$), and $S\subseteq S_{\mathbb{Q}}$ is a finite set of primes (`hS`).
--
--   **The automorphic input `hlink`.** This hypothesis asserts the existence of a smooth cusp realisation $R$ of $\Phi.\mathrm{toRawCentral}$ (the eigensystem with the same level and $a$, and with $b$ replaced by $v\mapsto \mathrm{N}(v)^{-1}b_v$) at the pins `productionPinsGeneral ℚ` — that is, a function on $\mathrm{GL}_2$ of the adeles of $\mathbb{Q}$, not identically zero, smooth and cuspidal for the central character `R.centralChar`, invariant under the level subgroup at $\Phi.\mathrm{level}$, and a Hecke and central eigenfunction with eigenvalues $a_v$ and $\mathrm{N}(v)^{-1}b_v$ outside the finite set `R.exceptionalSet` — such that `R.toFun` is continuous, together with a function $C$ of a finite adele and an adelic matrix, subject to the following clauses. First, `R.exceptionalSet ⊆ S`. Secondly, two archimedean constraints at each real place of $\mathbb{Q}$, for the case $P=\mathrm{principal}(u_1,a_1,u_2,a_2)$: $|\mathrm{Re}(u_1-u_2)|<1$, and for every nonzero integer $m$ with $u_1-u_2=m$ one has $a_1-a_2\ne m+1$ in $\mathbb{Z}/2$. Thirdly, at each real place $w$ the central character of $R$, transported to the full idele group along `Subgroup.topEquiv`, satisfies `IsArchCompAt` at $w$ with exponent $P.\mathrm{centralExponent}+1$ and sign $P.\mathrm{centralSign}$, i.e. its local component at $w$ is $x\mapsto \lVert x\rVert^{\mathrm{mult}(w)(P.\mathrm{centralExponent}+1)}(x/\lVert x\rVert)^{P.\mathrm{centralSign}}$.
--
--   Lastly, for every parity function $\mathrm{par}$ on the infinite places of $\mathbb{Q}$ with values in $\mathbb{Z}/2$ there exist $\varphi$ on adelic $\mathrm{GL}_2$, a family $W_{r}$ of functions $\mathbb{C}\to\mathbb{C}$ indexed by the infinite places, and integer weights $k$, such that (the clauses are summarised here in order): $\varphi$ is an `IsIsotypicCuspFormAt` form for the pins `productionPinsGeneral ℚ`, the central character `R.centralChar`, the level $\Phi.\mathrm{level}$ and the exceptional set $S$ — i.e. a continuous smooth cuspidal function, invariant under the level subgroup, with Hecke eigenvalue $a_v$ and central eigenvalue $\mathrm{N}(v)^{-1}b_v$ for $v\notin S$; $\varphi\ne 0$; $\varphi$ is fixed by right convolution `rightConv` against some factorisable test function $\alpha$; at each real place $\varphi$ satisfies `HasArchCharacterAt₀` for the weight character `archWeightCharAt hw (k w)`; the weights are pinned by $P$, namely $k(w)=\mathrm{signShift}(a_1+\mathrm{par}(w))+\mathrm{signShift}(a_2+\mathrm{par}(w))$ in the principal case and $k(w)=n+1$ in the discrete case; the Whittaker coefficient of $\varphi$ at $1$ with respect to `psiQ` factorises, in the sense that for every idele $a$ and every $g$ in `finiteAdelicGL2Subgroup ℚ` (the kernel of the archimedean projection) its value at $\mathrm{diagOne}(a)\,g$ equals $\bigl(\prod_w W_r(w)(\iota_w(a_\infty(w)))\bigr)\cdot C(a_{\mathrm{fin}})(g)$, the product being over all infinite places and $\iota_w$ the embedding `extensionEmbedding`; in the principal case with equal signs $a_1=a_2$ and $\mathrm{par}(w)=a_1$, $W_r(w)(-t)=(-1)^{a_1}W_r(w)(t)$ for all real $t$; in the discrete case $W_r(w)(t)=0$ for $t<0$; in the principal case with equal signs and $\mathrm{par}(w)=a_1+1$ there is $s_0$ such that for $\mathrm{Re}\,s>s_0$ the Mellin transform of $t\mapsto (W_r(w)(t)+(-1)^{a_1}W_r(w)(-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}\,(P.\mathrm{twist}\,0\,a_1).\mathrm{archFactor}(s)$; and for every $b\in\mathbb{Z}/2$ with $b=\mathrm{par}(w)$ or $b=\mathrm{par}(w)+P.\mathrm{centralSign}$ there is $s_0$ such that for $\mathrm{Re}\,s>s_0$ the Mellin transform of $t\mapsto (W_r(w)(t)+(-1)^{b}W_r(w)(-t))/t$ converges and equals $(P.\mathrm{twist}\,0\,b).\mathrm{archFactor}(s)$, where $\mathrm{archFactor}$ is the product of the $\Gamma_{\mathbb{R}}$- and $\Gamma_{\mathbb{C}}$-factors at the shifts of the parameter.
--
--   **The base-change character $\omega$.** A finite set $T_{\mathbb{Q}}$ of primes of $\mathcal{O}_{\mathbb{Q}}$ is given, and $\omega$ is a homomorphism from the ideles of $K$ to $\mathbb{C}^\times$ which is an admissible twist (`hω`: trivial on $K^\times$, continuous and unitary), subject to: `hωT`, for every prime $\mathfrak{P}$ of $\mathcal{O}_K$ whose prime below lies outside $T_{\mathbb{Q}}$, $\omega$ is unramified at $\mathfrak{P}$ and its value at the uniformiser idele at $\mathfrak{P}$ equals $(\mathrm{formalBaseChange}\ \mathbb{Q}\ K\ \Phi).b\,\mathfrak{P}=b_p^{f(\mathfrak{P}/p)}$ with $f$ the inertia degree `inertiaDeg'`; `hE`, every $\mathfrak{P}$ lying over a prime of $T_{\mathbb{Q}}$ belongs to $S_K$; `hωR` and `hωC`, the archimedean components of $\omega$ satisfy `IsArchCompAt` at each real place with exponent $P.\mathrm{centralExponent}$ and sign $P.\mathrm{centralSign}$, and at each complex place with exponent and twist those of the base-changed parameter $P.\mathrm{baseChange}$.
--
--   **The twisting character $\mu$.** Finally $\mu$ is an admissible twist of $K$ (`hμ`), subject to three hypotheses. `hoff`: there is no admissible twist $\eta$ of $\mathbb{Q}$ such that for every prime $\mathfrak{P}$ of $\mathcal{O}_K$ at which $\mu$ is unramified and whose prime $p$ below is unramified for $\eta$, the value of $\mu$ at the uniformiser idele at $\mathfrak{P}$ equals the value of $\eta$ at the uniformiser idele at $p$ raised to the inertia degree $f(\mathfrak{P}/p)$. `hdepth`: for every $w\in S_K$,
--   $$4\bigl(\mathrm{ord}_w(\Phi.\mathrm{level}\cdot\mathcal{O}_K)+n(\psi_w)+1\bigr)\le a(\mu_w),$$
--   where $\mathrm{ord}_w$ is `FractionalIdeal.count` at $w$ of the extension of the level, $n(\psi_w)$ is `addCharLevel` of the standard local additive character `psiLocal` at $w$, and $a(\mu_w)$ is `conductorExponentAt` of the local component `localChar μ w`. Archimedean data $u_R,a_R$ at the real places and $u_C,k_C$ at the complex places of $K$ are given, with `hcR` and `hcC`: $\mu$ satisfies `IsArchCompAt` at each real place $w$ with exponent $u_R(w)$ and sign $a_R(w)$, and at each complex place with exponent $u_C(w)$ and integer $k_C(w)$.
--
--   **Conclusion.** Let $D$ be the Rankin–Selberg $L$-datum $\mathrm{rsDatum}\ \mathbb{Q}\ S_{\mathbb{Q}}\ \Phi.a\ \Phi.b\ c$ with the four archimedean multisets described below, indexed by the primes $p\notin S_{\mathbb{Q}}$, where $c(\mathfrak{P})$ is the value of $\mu$ at the uniformiser idele at $\mathfrak{P}$ when $\mu$ is unramified at $\mathfrak{P}$ and $0$ otherwise; its norms are $\mathrm{N}(p)$, its Euler factor at $p$ is `rsEulerPoly` formed from $a_p$, $b_p$ and the induced local quantities `inducedE1`, `inducedE2`, `inducedE3` of $c$ at $p$, its dual Euler factor the same polynomial formed from $a_p/b_p$, $b_p^{-1}$ and the induced quantities of $\mathfrak{P}\mapsto c(\mathfrak{P})^{-1}$, with abscissa $1$, centre $1/2$ and degree $6$. The multiset `gammaR` is $\mathrm{twistedGammaR}$ for the constant family $P$ and the data $u_R,a_R$, i.e. the sum over the real places $w$ of $K$ of the $\Gamma_{\mathbb{R}}$-shifts of $P$ twisted by $(u_R(w),a_R(w))$; `gammaC` is $\mathrm{twistedGammaC}$, the sum over real places of the $\Gamma_{\mathbb{C}}$-shifts of those same twists together with the sum over complex places of the $\Gamma_{\mathbb{C}}$-shifts of $P.\mathrm{baseChange}$ twisted by $(u_C(w),k_C(w))$; `gammaRDual` and `gammaCDual` are the corresponding multisets formed from the duals $P.\mathrm{dual}$ and $(P.\mathrm{baseChange}).\mathrm{dual}$ and the negated parameters $-u_R$, $-u_C$, $-k_C$ (with $a_R$ unchanged).
--
--   The assertion is the conjunction of three statements. First, $D$ is well formed: every norm is at least $2$; every Euler polynomial and every dual Euler polynomial has constant term $1$ and degree at most $6$; and every shift $\nu$ occurring in any of the four multisets satisfies $-\mathrm{Re}\,\nu\le 1$. Secondly, $D$ converges: for every $s$ with $\mathrm{Re}\,s>1$ both families $p\mapsto \lVert P_p(\mathrm{N}(p)^{-s})-1\rVert$ and $p\mapsto\lVert P_p^{\vee}(\mathrm{N}(p)^{-s})-1\rVert$ are summable, and the values $D.\mathrm{LFun}(s)$ and $D.\mathrm{LFunDual}(s)$ are nonzero. Thirdly, $\mathrm{finiteConductor}\ K\ \mu\ S_K>0$, where this is the finite product over the primes $v$ of $\mathcal{O}_K$ of $1$ for $v\in S_K$ and of $\mathrm{N}(v)^{2\,\mathrm{pinnedExp}\,K\,\mu\,v}$ otherwise.
--
--   This result collects the three non-analytic inputs — well-formedness of the $L$-datum, absolute convergence together with non-vanishing of the Euler product and of its dual in the half-plane $\mathrm{Re}\,s>1$, and positivity of the finite conductor of $\mu$ away from $S_K$ — for the degree-six Rankin–Selberg datum attached to the formal base change of $\Phi$ to the cubic field $K$ twisted by $\mu$. It feeds the pinned-niceness statement for this datum, the statement producing an entire function equal to the archimedean factor times the $L$-function of the datum, and the corresponding global integral identity, all steps of the converse-theorem input to the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_wellFormed_and_converges_rsDatum_and_finiteConductor_pos_of_le_conductorExponentAt_of_not_exists_eq_pow_inertiaDeg.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Mathlib.Analysis.MellinTransform
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ArchBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open scoped nonZeroDivisors
open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.wellFormed_and_converges_rsDatum_and_finiteConductor_pos_of_le_conductorExponentAt_of_not_exists_eq_pow_inertiaDeg
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
    (hdepth : ∀ w : ↥SK,
      4 * (FractionalIdeal.count K w.1
            ((Φ.level.map (algebraMap (𝓞 ℚ) (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) +
          LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w.1) + 1) ≤
        LanglandsTunnell.TateLocal.conductorExponentAt K w.1 (localChar μ w.1))
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ)
    (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ)
    (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (hcR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (hcC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw)) :
    (rsDatum ℚ SQ Φ.a Φ.b
    (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
    (twistedGammaR K (archOfParamR K P) uR aR)
    (twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC)
    (twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR)
    (twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual)
    (fun w hw => (archOfParamC K P w hw).dual)
    (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw))).WellFormed ∧
    (rsDatum ℚ SQ Φ.a Φ.b
    (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
    (twistedGammaR K (archOfParamR K P) uR aR)
    (twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC)
    (twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR)
    (twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual)
    (fun w hw => (archOfParamC K P w hw).dual)
    (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw))).Converges ∧
    0 < (finiteConductor K μ SK) := by sorry
