-- Prove2me | Theorems.Thm_GaussPart_Supplement_theorem_5_12
-- name    : GaussPart.Supplement.theorem_5_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:09:50.287707+00:00
-- url     : https://prove2.me/theorems/5a783cdb-cd8a-4622-aaa9-600dfe792a7a
-- title:
--   Theorem 5.12 — PUI learning intersections of $k$ halfspaces with $m=O(\log k+q\log(q/(\sigma\epsilon p_+)))$
-- statement:
--   **Setting.** Let $k,d\in\mathbb N_+$, $\mathcal F_k$ the class of intersections of at most $k$ halfspaces (constants included), $\epsilon\in(0,1/2)$, $q\ge1$, $\sigma\in(0,1]$. Let $D=\mathcal N(0,I_d)$ and let $D^*$ be $(q,\sigma)$-smooth with respect to $D$. The target $f$ is unknown; $p_+:=D^*(f=1)>0$ and $D^*_+:=D^*\mid\{f=1\}$. Set
--   $$
--   m=\Bigl\lceil C\Bigl(\log(2k)+q\log\frac{2q}{\sigma\epsilon p_+}\Bigr)\Bigr\rceil
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
--   The dimension exponent depends only logarithmically on $k$ and $1/\epsilon$.
--
--   **Formalization Note** The constant of $(2m)^{O(m)}$ and the polynomial are universal and chosen with $C$; the learner sees i.i.d. samples of $D^*_+$ only and is given $p_+=D^*(f=1)$ exactly.
--
--   Differences from the source:
--   - encoding: there is an algorithm that draws n samples and runs in poly(n) time → one program of the published GaussMixHH sampling RAM restricted by ArithmeticOnly, with an evaluator program computing h within the same budget; sample count ≤ n and work ≤ C·n^C on every sample stream; success on a measurable set of streams; reason: the machine model of the base mission; the paper's algorithm and time bound read in it
--   - encoding: m := ⌈C(…)⌉ for a sufficiently large universal C; N = d^m exp((2m)^{O(m)}); poly(N) → ∃ C > 0 and naturals C′, C″ chosen first; N = d^m·exp((2m)^{C′m}), work ≤ C″N^{C″}; reason: a larger C only enlarges N, so ∃ C is the page's 'sufficiently large'
--   - encoding: the parameters fixed before 'there is an algorithm' → one program, chosen after the class, given ϵ, σ, p₊, q in memory; reason: a finite program with rational literals cannot hard-code real parameters or class numbers; the program may depend on the class, never on the target or the distribution
--   - encoding: halfspaces → closed halfspaces w·x ≤ t; reason: hyperplanes are null under a distribution smooth with respect to N(0, I_d)
--   - encoding: a hypothesis h : ℝ^d → {±1} and Pr[h(x) ≠ y] → h(x) = 1 if the evaluator halts within the work budget with output 1, else −1; probabilities in [0, ∞] (outer measure when h is not shown measurable); reason: the output of a machine is a description; bounding the error by an outer measure only strengthens the claim
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Theorem 5.12, p.53 (PDF p.55); informal version Theorem 1.9 (i), p.5

import Mathlib
import Definitions.Def_GaussMixHH_Machine
import Definitions.Def_GaussPart_IsSmooth
import Definitions.Def_GaussPart_ArithmeticOnly
import Definitions.Def_GaussPart_Supplement_Learner
import Definitions.Def_GaussPart_Supplement_Halfspaces

open MeasureTheory ProbabilityTheory

namespace GaussPart

namespace Supplement

/-- **Theorem 5.12** (PUI Learning Intersections of Halfspaces).

I. Diakonikolas, G. Iakovidis, D. M. Kane, M. Ma, *Gaussian Partitioning for Reliable Learning of
Multi-Index Models*, arXiv:2611.05264 (copy with sha256 7e0ca6d4…), Theorem 5.12, p.53 (PDF p.55);
informal version Theorem 1.9 (i), p.5.

"Let k, d ∈ ℕ₊, ϵ ∈ (0, 1/2), q ≥ 1, and σ ∈ (0, 1]. Let D = N(0, I_d) and let D∗ be a distribution
that is (q, σ)-smooth with respect to D. Let f ∈ F_k be an unknown target intersection of k
halfspaces, and set p+ := D∗(f = 1) > 0, D∗_+ := D∗ | {f = 1}. Set
m := ⌈C(log(2k) + q log(2q/(σϵp+)))⌉ for a sufficiently large universal constant C > 0. There is an
algorithm which, given ϵ, σ, p+, q and sample access to D∗_+, draws at most N = d^m exp((2m)^{O(m)})
samples. The algorithm runs in time polynomial in N and, with probability at least 2/3, outputs a
hypothesis h : ℝ^d → {±1} satisfying Pr_{x∼D∗}[h(x) ≠ f(x)] ≤ ϵ."

**Formalization Note.**
* `F_k` is `IntersectionClass d k` (at most `k` closed halfspaces, constants included, §5.3 p.53).
* `C > 0` (real), the constant `C′` of `(2m)^{O(m)}` and the constant `C″` of `poly(N) = C″N^{C″}` are
  chosen first; a larger `C` only enlarges `N`, so `∃ C` is the page's "sufficiently large `C`". The
  program may depend on the class (on `d, k`) and is uniform in `ϵ, σ, q`, the target and `D∗`; it is
  given `ϵ, σ, p₊, q` with `p₊ = D∗(f = 1)` exactly.
* The learner reads i.i.d. samples of `D∗₊ = cond D∗ {f = 1}` only; the error is under `D∗`. Bounds on
  every stream, success on a measurable set of streams, the evaluated hypothesis: as in
  `theorem_4_2`. -/
theorem theorem_5_12 :
    ∃ C : ℝ, 0 < C ∧ ∃ C' C'' : ℕ,
    ∀ (d k : ℕ), 1 ≤ d → 1 ≤ k →
    ∃ (P : GaussMixHH.Program) (_ : GaussMixHH.Admissible P) (_ : ArithmeticOnly P)
      (E : GaussMixHH.Program) (_ : GaussMixHH.Admissible E) (_ : ArithmeticOnly E),
    ∀ (ε q σ : ℝ), 0 < ε → ε < 1 / 2 → 1 ≤ q → 0 < σ → σ ≤ 1 →
    ∀ f ∈ IntersectionClass d k, ∀ Ds : Measure (Vec d), IsProbabilityMeasure Ds →
      IsSmooth (stdGaussian (Vec d)) Ds q σ → 0 < Ds {x | f x = 1} →
      let pPos : ℝ := (Ds {x | f x = 1}).toReal
      let m : ℕ := ⌈C * (Real.log (2 * (k : ℝ)) + q * Real.log (2 * q / (σ * ε * pPos)))⌉₊
      let N : ℝ := (d : ℝ) ^ m * Real.exp ((2 * (m : ℝ)) ^ (C' * m))
      let inp : List ℝ := [ε, σ, pPos, q]
      RunsWithin P d inp N (C'' * N ^ C'') ∧
      SucceedsWith P d inp (Measure.infinitePi fun _ : ℕ => cond Ds {x | f x = 1}) (2 / 3)
        (fun s => Ds {x | hyp E d (C'' * N ^ C'') s x ≠ f x} ≤ ENNReal.ofReal ε) := by sorry

end Supplement

end GaussPart
