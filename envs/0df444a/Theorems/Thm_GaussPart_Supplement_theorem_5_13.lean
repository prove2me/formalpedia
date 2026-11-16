-- Prove2me | Theorems.Thm_GaussPart_Supplement_theorem_5_13
-- name    : GaussPart.Supplement.theorem_5_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:10:39.840432+00:00
-- url     : https://prove2.me/theorems/9eca7929-ebd9-495f-943d-6e0e3487f075
-- title:
--   Theorem 5.13 — PUI learning $K$-dimensional convex sets with $m=O(K+q\log(q/(\sigma\epsilon p_+)))$
-- statement:
--   **Setting.** Let $K,d\in\mathbb N_+$, $\mathcal C_K$ the class of Boolean $K$-MIMs on $\mathbb R^d$ whose positive region is convex, $\epsilon\in(0,1/2)$, $q\ge1$, $\sigma\in(0,1]$. Let $D=\mathcal N(0,I_d)$ and let $D^*$ be $(q,\sigma)$-smooth with respect to $D$. The target $f$ is unknown; $p_+:=D^*(f=1)>0$ and $D^*_+:=D^*\mid\{f=1\}$. Set
--   $$
--   m=\Bigl\lceil C\Bigl(K+q\log\frac{2q}{\sigma\epsilon p_+}\Bigr)\Bigr\rceil
--   $$
--   for a sufficiently large universal constant $C>0$.
--
--   **Theorem.** There is an algorithm which, given $\epsilon,\sigma,p_+,q$ and sample access to $D^*_+$, draws at most
--   $$
--   N=d^m\exp\bigl((2m)^{O(m)}\bigr)
--   $$
--   samples, runs in time polynomial in $N$, and with probability at least $2/3$ outputs $h:\mathbb R^d\to\{\pm1\}$ with
--   $$
--   \Pr_{x\sim D^*}[h(x)\neq f(x)]\le\epsilon .
--   $$
--
--   The dimension exponent is linear in $K$ and logarithmic in $1/\epsilon$.
--
--   **Formalization Note** The constant of $(2m)^{O(m)}$ and the polynomial are universal and chosen with $C$; the learner sees i.i.d. samples of $D^*_+$ only and is given $p_+=D^*(f=1)$ exactly.
--
--   Differences from the source:
--   - encoding: there is an algorithm that draws n samples and runs in poly(n) time → one program of the published GaussMixHH sampling RAM restricted by ArithmeticOnly, with an evaluator program computing h within the same budget; sample count ≤ n and work ≤ C·n^C on every sample stream; success on a measurable set of streams; reason: the machine model of the base mission; the paper's algorithm and time bound read in it
--   - encoding: m := ⌈C(…)⌉ for a sufficiently large universal C; N = d^m exp((2m)^{O(m)}); poly(N) → ∃ C > 0 and naturals C′, C″ chosen first; N = d^m·exp((2m)^{C′m}), work ≤ C″N^{C″}; reason: a larger C only enlarges N, so ∃ C is the page's 'sufficiently large'
--   - encoding: the parameters fixed before 'there is an algorithm' → one program, chosen after the class, given ϵ, σ, p₊, q in memory; reason: a finite program with rational literals cannot hard-code real parameters or class numbers; the program may depend on the class, never on the target or the distribution
--   - encoding: a hypothesis h : ℝ^d → {±1} and Pr[h(x) ≠ y] → h(x) = 1 if the evaluator halts within the work budget with output 1, else −1; probabilities in [0, ∞] (outer measure when h is not shown measurable); reason: the output of a machine is a description; bounding the error by an outer measure only strengthens the claim
--   - reading: a K-dimensional convex set f ∈ C_K → a Borel measurable ±1-valued K-MIM with convex positive region; reason: Boolean functions are Borel measurable (Definition A.1)
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Theorem 5.13, p.54 (PDF p.56); C_K, Corollary 4.8, p.43

import Mathlib
import Definitions.Def_GaussMixHH_Machine
import Definitions.Def_GaussPart_IsSmooth
import Definitions.Def_GaussPart_ArithmeticOnly
import Definitions.Def_GaussPart_Supplement_Learner
import Definitions.Def_GaussPart_Supplement_Halfspaces

open MeasureTheory ProbabilityTheory

namespace GaussPart

namespace Supplement

/-- **Theorem 5.13** (PUI Learning Low-Dimensional Convex Sets).

I. Diakonikolas, G. Iakovidis, D. M. Kane, M. Ma, *Gaussian Partitioning for Reliable Learning of
Multi-Index Models*, arXiv:2611.05264 (copy with sha256 7e0ca6d4…), Theorem 5.13, p.54 (PDF p.56).

"Let K, d ∈ ℕ₊, ϵ ∈ (0, 1/2), q ≥ 1, and σ ∈ (0, 1]. Let D = N(0, I_d) and let D∗ be a distribution
that is (q, σ)-smooth with respect to D. Let f ∈ C_K be an unknown target K-dimensional convex set,
and set p+ := D∗(f = 1) > 0, D∗_+ := D∗ | {f = 1}. Set m := ⌈C(K + q log(2q/(σϵp+)))⌉ for a
sufficiently large universal constant C > 0. There is an algorithm which, given ϵ, σ, p+, q and sample
access to D∗_+, draws at most N = d^m exp((2m)^{O(m)}) samples. The algorithm runs in time polynomial
in N and, with probability at least 2/3, outputs a hypothesis h : ℝ^d → {±1} satisfying
Pr_{x∼D∗}[h(x) ≠ f(x)] ≤ ϵ."

**Formalization Note.**
* `C_K` is `ConvexClass d K`: the Borel measurable `±1`-valued `K`-MIMs on `ℝᵈ` whose positive
  region `{f = 1}` is convex (Corollary 4.8, p.43).
* `C > 0` (real), the constant `C′` of `(2m)^{O(m)}` and the constant `C″` of `poly(N) = C″N^{C″}` are
  chosen first; a larger `C` only enlarges `N`, so `∃ C` is the page's "sufficiently large `C`". The
  program may depend on the class (on `d, K`) and is uniform in `ϵ, σ, q`, the target and `D∗`; it is
  given `ϵ, σ, p₊, q` with `p₊ = D∗(f = 1)` exactly.
* The learner reads i.i.d. samples of `D∗₊ = cond D∗ {f = 1}` only; the error is under `D∗`. Bounds on
  every stream, success on a measurable set of streams, the evaluated hypothesis: as in
  `theorem_4_2`. -/
theorem theorem_5_13 :
    ∃ C : ℝ, 0 < C ∧ ∃ C' C'' : ℕ,
    ∀ (K d : ℕ), 1 ≤ K → 1 ≤ d →
    ∃ (P : GaussMixHH.Program) (_ : GaussMixHH.Admissible P) (_ : ArithmeticOnly P)
      (E : GaussMixHH.Program) (_ : GaussMixHH.Admissible E) (_ : ArithmeticOnly E),
    ∀ (ε q σ : ℝ), 0 < ε → ε < 1 / 2 → 1 ≤ q → 0 < σ → σ ≤ 1 →
    ∀ f ∈ ConvexClass d K, ∀ Ds : Measure (Vec d), IsProbabilityMeasure Ds →
      IsSmooth (stdGaussian (Vec d)) Ds q σ → 0 < Ds {x | f x = 1} →
      let pPos : ℝ := (Ds {x | f x = 1}).toReal
      let m : ℕ := ⌈C * ((K : ℝ) + q * Real.log (2 * q / (σ * ε * pPos)))⌉₊
      let N : ℝ := (d : ℝ) ^ m * Real.exp ((2 * (m : ℝ)) ^ (C' * m))
      let inp : List ℝ := [ε, σ, pPos, q]
      RunsWithin P d inp N (C'' * N ^ C'') ∧
      SucceedsWith P d inp (Measure.infinitePi fun _ : ℕ => cond Ds {x | f x = 1}) (2 / 3)
        (fun s => Ds {x | hyp E d (C'' * N ^ C'') s x ≠ f x} ≤ ENNReal.ofReal ε) := by sorry

end Supplement

end GaussPart
