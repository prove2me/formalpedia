-- Prove2me | Theorems.Thm_GaussPart_Supplement_theorem_5_4
-- name    : GaussPart.Supplement.theorem_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:09:11.736274+00:00
-- url     : https://prove2.me/theorems/3a240820-129c-4dc6-ba04-1f65e9d3ccda
-- title:
--   Theorem 5.4 — SQ lower bound for PUI learning of Gaussian MIMs: $2^{d^{\Omega(1)}}$ queries or tolerance $d^{-\Omega(m^*)}$
-- statement:
--   **Setting.** Let $d,K,m^*\in\mathbb Z_+$ with $m^*\ge2$ and $\max\{K,m^*\}\le d^c$, for a sufficiently small absolute constant $c>0$ and sufficiently large $d$; let $\sigma,\epsilon\in(0,1]$ and $q\ge1$. Let $\mathcal F$ be a class of Boolean functions on $\mathbb R^d$ containing an $f$ such that
--
--   1. $f(x)=g(Wx)$ for a $K\times d$ matrix $W$ with $WW^\top=I_K$;
--   2. $\mathcal F$ contains every rotation $x\mapsto g(Ux)$, $UU^\top=I_K$;
--   3. some $D^*$ that is $(q,\sigma)$-smooth with respect to $\mathcal N(0,I_d)$ has $p_+:=\Pr_{D^*}[f=1]\in(0,1)$, $\Pr_{D^*}[f=-1]\ge\epsilon$, $(\sigma\epsilon)^q\ge d^{-cm^*}$, $p_+\ge d^{-cm^*}$, and $D^*_+=D^*\mid\{f=1\}$ matches the moments of $\mathcal N(0,I_d)$ exactly through degree $m^*$.
--
--   **Theorem.** Any SQ algorithm that learns $\mathcal F$ over distributions that are $(q,\sigma)$-smooth with respect to $\mathcal N(0,I_d)$, using SQ access only to the positive conditional distribution, to error $p_+(\sigma\epsilon)^q/2$ with probability at least $2/3$, requires either
--   $$
--   2^{d^{\Omega(1)}}\ \text{queries}\qquad\text{or a query of tolerance at most}\qquad d^{-\Omega(m^*)} .
--   $$
--
--   This matches the $d^{m^*}$ dependence of the algorithm of Theorem 5.3 qualitatively.
--
--   **Formalization Note** The constants $c$, $d_0$ and the two $\Omega$-constants are existential and chosen first; "learns" quantifies over every target in $\mathcal F$, every smooth $D'$ with $D'(f'=1)\ge p_+$ and every valid oracle for the positive conditional.
--
--   Differences from the source:
--   - encoding: any SQ algorithm (Definition A.4) that makes no query of tolerance at most τ₀ → every randomized adaptive SQ algorithm of the published SQAlg type whose every query is a measurable [−1,1]-valued function with tolerance > τ₀, against adversarial trajectory-dependent oracles; reason: the published SQ model; states no run reaches can be changed without changing any run
--   - reading: requires 2^{d^{Ω(1)}} queries → on some admissible instance, against some valid oracle, some run makes at least 2^{d^{c₁}} queries with positive probability; reason: worst-case query complexity of a randomized SQ algorithm
--   - reading: learns F over distributions that are (q, σ)-smooth, using SQ access only to D∗₊ → for every f′ ∈ F, every (q, σ)-smooth D′ with D′(f′ = 1) ≥ p₊ and every valid oracle for D′ | {f′ = 1}, the output law gives mass ≥ 2/3 to h with Pr_{D′}[h ≠ f′] ≤ p₊(σϵ)^q/2; reason: Definition 1.7: the PUI learner is given the lower bound p₊
--   - encoding: D∗₊ and N(0, I_d) match moments through degree m∗ → MatchesMoments with W = ℝ^d, degree m∗ and slack 0; reason: exact directional moment matching
--   - encoding: sufficiently small c, sufficiently large d, Ω(·) → ∃ c > 0, ∃ d₀, ∃ c₁ c₂ > 0 chosen before d and every parameter; reason: universal constants
--   - reading: F ⊆ {ℝ^d → {±1}} a class of Boolean functions → every member of F is a Borel measurable ±1-valued function (IsBoolFn); reason: Boolean functions are Borel measurable in this paper (Definition A.1); it makes D∗(f = 1) and D∗₊ the page's objects
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Theorem 5.4, p.45 (PDF p.47); informal version Theorem 1.8 (ii), p.5; Definition A.4, p.70

import Mathlib
import Definitions.Def_PrivLearn_SQSim_SQAlg
import Definitions.Def_GaussPart_IsSmooth
import Definitions.Def_GaussPart_MatchesMoments
import Definitions.Def_GaussPart_Supplement_BoolFn
import Definitions.Def_GaussPart_Supplement_SQ

open MeasureTheory ProbabilityTheory Matrix PrivLearn.SQSim

namespace GaussPart

namespace Supplement

/-- **Theorem 5.4** (SQ Lower Bounds for PUI Learning of Gaussian MIMs).

I. Diakonikolas, G. Iakovidis, D. M. Kane, M. Ma, *Gaussian Partitioning for Reliable Learning of
Multi-Index Models*, arXiv:2611.05264 (copy with sha256 7e0ca6d4…), Theorem 5.4, p.45 (PDF p.47);
informal version Theorem 1.8 (ii), p.5.

"Let d, K, m∗ ∈ ℤ₊ with m∗ ≥ 2 and max{K, m∗} ≤ d^c, for a sufficiently small absolute constant
c > 0 and sufficiently large d. Let σ, ϵ ∈ (0, 1] and q ≥ 1. Let F ⊆ {ℝ^d → {±1}} be a class of
Boolean functions. Suppose there exists f ∈ F such that: 1. f depends only on the projection onto a
subspace V ⊆ ℝ^d of dimension K, i.e., f(x) = g(Wx) for W ∈ ℝ^{K×d} satisfying WW^⊤ = I_K.
2. F contains every rotation of f, i.e., x ↦ g(Ux) belongs to F for every U ∈ ℝ^{K×d} satisfying
UU^⊤ = I_K. 3. There exists a distribution D∗ that is (q, σ)-smooth with respect to N(0, I_d) such
that p+ := Pr_{x∼D∗}[f(x) = 1] ∈ (0, 1), Pr_{x∼D∗}[f(x) = −1] ≥ ϵ, and (σϵ)^q, p+ ≥ d^{−cm∗}.
Moreover, D∗_+ := D∗ | {f(x) = 1} and N(0, I_d) match moments through degree m∗. Then any SQ
algorithm that learns F over distributions that are (q, σ)-smooth with respect to N(0, I_d), using
SQ access only to the positive conditional distribution D∗_+, to error p+(σϵ)^q/2 with probability
at least 2/3, requires either 2^{d^{Ω(1)}} queries or a query of tolerance at most d^{−Ω(m∗)}."

**Formalization Note.**
* `c`, the threshold `d₀` of "sufficiently large `d`", and the constants `c₁, c₂` of the two `Ω(·)`
  are chosen first. Exact moment matching through degree `m∗` is the published `MatchesMoments` with
  `W = ⊤` and slack `0`.
* SQ algorithms are the published `PrivLearn.SQSim.SQAlg` (randomized, adaptive, any state type);
  validity of an oracle is the published `IsValidOracle` (adversarial, trajectory-dependent answers).
  "No query of tolerance at most `d^{−c₂m∗}`" is `TolAbove` (every query a measurable `[−1, 1]`-valued
  function, each with its own tolerance). "Learns" is: for every target `f′ ∈ F` and every
  `(q, σ)`-smooth `D′` with `D′(f′ = 1) ≥ p₊` (the PUI lower bound `p₊` of Definition 1.7), against
  every valid oracle for `D′₊ = cond D′ {f′ = 1}`, the output law gives mass `≥ 2/3` to hypotheses `h`
  with `Pr_{D′}[h ≠ f′] ≤ p₊(σϵ)^q/2`. "Requires `2^{d^{c₁}}` queries" is: on some such instance,
  against some valid oracle, some run with positive probability makes at least `2^{d^{c₁}}` queries.
* "A class of Boolean functions" is a class of Borel measurable `±1`-valued functions (`IsBoolFn`),
  the paper's convention for Boolean functions (Definition A.1); this makes `f` and its rotations
  measurable, so `D∗(f = 1)` and `D∗₊` are the page's.
* There is no time bound: the lower bound is information-theoretic. -/
theorem theorem_5_4 :
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
    ∀ (d K m : ℕ), d₀ ≤ d → 1 ≤ K → 2 ≤ m → (K : ℝ) ≤ (d : ℝ) ^ c → (m : ℝ) ≤ (d : ℝ) ^ c →
    ∀ (σ ε q : ℝ), 0 < σ → σ ≤ 1 → 0 < ε → ε ≤ 1 → 1 ≤ q →
    ∀ F : Set (Vec d → ℝ), (∀ f ∈ F, IsBoolFn f) →
    ∀ (g : Vec K → ℝ) (W : Matrix (Fin K) (Fin d) ℝ), W * Wᵀ = 1 →
      (fun x => g (matVec W x)) ∈ F →
      (∀ U : Matrix (Fin K) (Fin d) ℝ, U * Uᵀ = 1 → (fun x => g (matVec U x)) ∈ F) →
    ∀ Ds : Measure (Vec d), IsProbabilityMeasure Ds → IsSmooth (stdGaussian (Vec d)) Ds q σ →
      let f : Vec d → ℝ := fun x => g (matVec W x)
      let pPos : ℝ := (Ds {x | f x = 1}).toReal
      0 < pPos → pPos < 1 → ENNReal.ofReal ε ≤ Ds {x | f x = -1} →
      (d : ℝ) ^ (-(c * m)) ≤ (σ * ε) ^ q → (d : ℝ) ^ (-(c * m)) ≤ pPos →
      MatchesMoments (stdGaussian (Vec d)) (cond Ds {x | f x = 1}) ⊤ m 0 →
    ∀ (St : Type) (B : SQAlg (Vec d) (Vec d → ℝ) St),
      TolAbove B ((d : ℝ) ^ (-(c₂ * m))) →
      (∀ f' ∈ F, ∀ D' : Measure (Vec d), IsProbabilityMeasure D' →
        IsSmooth (stdGaussian (Vec d)) D' q σ → ENNReal.ofReal pPos ≤ D' {x | f' x = 1} →
        ∀ O : List St → ℝ, B.IsValidOracle (cond D' {x | f' x = 1}) O →
          (2 / 3 : ENNReal) ≤ successMass B O
            {h | D' {x | h x ≠ f' x} ≤ ENNReal.ofReal (pPos * (σ * ε) ^ q / 2)}) →
      ∃ f' ∈ F, ∃ D' : Measure (Vec d), IsProbabilityMeasure D' ∧
        IsSmooth (stdGaussian (Vec d)) D' q σ ∧ ENNReal.ofReal pPos ≤ D' {x | f' x = 1} ∧
        ∃ O : List St → ℝ, B.IsValidOracle (cond D' {x | f' x = 1}) O ∧
          MakesManyQueries B O ((2 : ℝ) ^ ((d : ℝ) ^ c₁)) := by sorry

end Supplement

end GaussPart
