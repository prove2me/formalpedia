-- Prove2me | Theorems.Thm_GaussPart_Supplement_theorem_1_12
-- name    : GaussPart.Supplement.theorem_1_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:13:15.66554+00:00
-- url     : https://prove2.me/theorems/85ff7565-c115-45e9-a9a3-62853950352d
-- title:
--   Theorem 1.12 (Corollary 6.4) — reliable learning of intersections and unions of $k$ halfspaces
-- statement:
--   This is Theorem 1.12 at the precision of its formal version, Corollary 6.4.
--
--   **Setting.** Let $k,d\in\mathbb N_+$, $\epsilon\in(0,1/2)$, $q\ge1$, $\sigma\in(0,1]$, and let $D$ be a distribution on $\mathbb R^d\times\{\pm1\}$ whose x-marginal is $(q,\sigma)$-smooth with respect to $\mathcal N(0,I_d)$; the labels are arbitrary. Set
--   $$
--   m=\Bigl\lceil C\Bigl(\log(2k)+q\log\frac{2q}{\sigma\epsilon}\Bigr)\Bigr\rceil
--   $$
--   for a sufficiently large universal constant $C>0$.
--
--   **Theorem.** There is an algorithm which, given $\epsilon,\sigma,q$ and sample access to $D$, uses at most
--   $$
--   N=d^m\exp\bigl((2m)^{O(m)}\bigr)
--   $$
--   labeled samples, runs in time polynomial in $N$, and negatively reliably learns the class $\mathcal F_k$ of intersections of at most $k$ halfspaces with probability at least $2/3$. With the same sample and running-time bounds, the unions of at most $k$ halfspaces are positively reliably learnable under $D$.
--
--   The dimension exponent is logarithmic in $k$ and in $1/\epsilon$, whereas fully agnostic learning of a single halfspace already has SQ complexity $d^{\Omega(1/\epsilon^2)}$.
--
--   **Formalization Note** The constants are universal and serve both clauses; the programs may depend on $d,k$.
--
--   Differences from the source:
--   - encoding: there is an algorithm that draws n samples and runs in poly(n) time → one program of the published GaussMixHH sampling RAM restricted by ArithmeticOnly, with an evaluator program computing h within the same budget; sample count ≤ n and work ≤ C·n^C on every sample stream; success on a measurable set of streams; reason: the machine model of the base mission; the paper's algorithm and time bound read in it
--   - encoding: m := ⌈C(…)⌉ for a sufficiently large universal C; N = d^m exp((2m)^{O(m)}); poly(N) → ∃ C > 0 and naturals C′, C″ chosen first and shared by both clauses; N = d^m·exp((2m)^{C′m}), work ≤ C″N^{C″}; reason: a larger C only enlarges N, so ∃ C is the page's 'sufficiently large'
--   - encoding: the parameters fixed before 'there is an algorithm' → one program, chosen after the class, given ϵ, σ, q in memory; reason: a finite program with rational literals cannot hard-code real parameters or class numbers; the program may depend on the class, never on the target or the distribution
--   - encoding: halfspaces → closed halfspaces w·x ≤ t; intersections include the constants, unions the constant −1 (empty union); reason: hyperplanes are null under a smooth marginal
--   - encoding: a hypothesis h : ℝ^d → {±1} and Pr[h(x) ≠ y] → h(x) = 1 if the evaluator halts within the work budget with output 1, else −1; probabilities in [0, ∞] (outer measure when h is not shown measurable); reason: the output of a machine is a description; bounding the error by an outer measure only strengthens the claim
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Theorem 1.12, p.6 (PDF p.8); formal version Corollary 6.4, pp.62–63 (PDF pp.64–65)

import Mathlib
import Definitions.Def_GaussMixHH_Machine
import Definitions.Def_GaussPart_IsSmooth
import Definitions.Def_GaussPart_ArithmeticOnly
import Definitions.Def_GaussPart_Supplement_Learner
import Definitions.Def_GaussPart_Supplement_LabeledLaw
import Definitions.Def_GaussPart_Supplement_Halfspaces

open MeasureTheory ProbabilityTheory

namespace GaussPart

namespace Supplement

/-- **Theorem 1.12** (Reliable Learning of Intersections and Unions), stated at the precision of its
formal version **Corollary 6.4** (Reliable Learning of Intersections and Unions of Halfspaces).

I. Diakonikolas, G. Iakovidis, D. M. Kane, M. Ma, *Gaussian Partitioning for Reliable Learning of
Multi-Index Models*, arXiv:2611.05264 (copy with sha256 7e0ca6d4…), Theorem 1.12, p.6 (PDF p.8);
Corollary 6.4, pp.62–63 (PDF pp.64–65).

Corollary 6.4: "Let k, d ∈ ℕ₊, ϵ ∈ (0, 1/2), q ≥ 1, and σ ∈ (0, 1]. Let D be a distribution over
ℝ^d × {±1} whose x-marginal is (q, σ)-smooth with respect to N(0, I_d). Set
m := ⌈C(log(2k) + q log(2q/(σϵ)))⌉ for a sufficiently large universal constant C > 0. There is an
algorithm which, given ϵ, σ, q and sample access to D, uses at most N = d^m exp((2m)^{O(m)}) labeled
samples, runs in time polynomial in N, and negatively reliably learns the class F_k of intersections
of at most k halfspaces with probability at least 2/3. With the same sample and running-time bounds,
unions of at most k halfspaces are positively reliably learnable under D."

**Formalization Note.**
* `C > 0`, the constant `C′` of `(2m)^{O(m)}` and the constant `C″` of `poly(N) = C″N^{C″}` are chosen
  first and serve both clauses. The programs may depend on the class (on `d, k`) and are uniform in
  `ϵ, σ, q` and `D`; they are given `ϵ, σ, q`.
* `F_k = IntersectionClass d k`, unions `UnionClass d k` (closed halfspaces, constants included).
  Reliable learning is `NegReliable` / `PosReliable` (Definition 6.1); labels are arbitrary.
* Labeled samples, bounds on every stream, success on a measurable set, evaluated hypotheses: as in
  `theorem_4_2`. -/
theorem theorem_1_12 :
    ∃ C : ℝ, 0 < C ∧ ∃ C' C'' : ℕ,
    ∀ (d k : ℕ), 1 ≤ d → 1 ≤ k →
    (∃ (P : GaussMixHH.Program) (_ : GaussMixHH.Admissible P) (_ : ArithmeticOnly P)
      (E : GaussMixHH.Program) (_ : GaussMixHH.Admissible E) (_ : ArithmeticOnly E),
      ∀ (ε q σ : ℝ), 0 < ε → ε < 1 / 2 → 1 ≤ q → 0 < σ → σ ≤ 1 →
        let m : ℕ := ⌈C * (Real.log (2 * (k : ℝ)) + q * Real.log (2 * q / (σ * ε)))⌉₊
        let N : ℝ := (d : ℝ) ^ m * Real.exp ((2 * (m : ℝ)) ^ (C' * m))
        let inp : List ℝ := [ε, σ, q]
        RunsWithin P (d + 1) inp N (C'' * N ^ C'') ∧
        ∀ D : Measure (Vec d × ℝ), IsLabeledLaw D →
          IsSmooth (stdGaussian (Vec d)) (D.map Prod.fst) q σ →
          SucceedsWith P (d + 1) inp (labeledStream D) (2 / 3)
            (fun s => NegReliable (IntersectionClass d k) D ε (hyp E d (C'' * N ^ C'') s))) ∧
    (∃ (P : GaussMixHH.Program) (_ : GaussMixHH.Admissible P) (_ : ArithmeticOnly P)
      (E : GaussMixHH.Program) (_ : GaussMixHH.Admissible E) (_ : ArithmeticOnly E),
      ∀ (ε q σ : ℝ), 0 < ε → ε < 1 / 2 → 1 ≤ q → 0 < σ → σ ≤ 1 →
        let m : ℕ := ⌈C * (Real.log (2 * (k : ℝ)) + q * Real.log (2 * q / (σ * ε)))⌉₊
        let N : ℝ := (d : ℝ) ^ m * Real.exp ((2 * (m : ℝ)) ^ (C' * m))
        let inp : List ℝ := [ε, σ, q]
        RunsWithin P (d + 1) inp N (C'' * N ^ C'') ∧
        ∀ D : Measure (Vec d × ℝ), IsLabeledLaw D →
          IsSmooth (stdGaussian (Vec d)) (D.map Prod.fst) q σ →
          SucceedsWith P (d + 1) inp (labeledStream D) (2 / 3)
            (fun s => PosReliable (UnionClass d k) D ε (hyp E d (C'' * N ^ C'') s))) := by sorry

end Supplement

end GaussPart
