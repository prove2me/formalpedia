-- Prove2me | Theorems.Thm_GaussPart_Supplement_theorem_6_2
-- name    : GaussPart.Supplement.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:11:56.698221+00:00
-- url     : https://prove2.me/theorems/cca4d791-53bd-45ea-8216-ad21bb619fb9
-- title:
--   Theorem 6.2 — agnostic negative reliable learning in $d^{m}$ samples, $m=m^*(c\epsilon,\Delta,c\sigma\epsilon^3/q,2q)$
-- statement:
--   **Setting.** Let $\mathcal F$ be a class of Boolean functions on $\mathbb R^d$ that is closed under affine restrictions, has finite Gaussian surface area $\Gamma(\mathcal F)$ and contains the constant function $1$. Let $D$ be a distribution on $\mathbb R^d\times\{\pm1\}$ whose x-marginal is $(q,\sigma)$-smooth with respect to $\mathcal N(0,I_d)$ ($q\ge1$, $\sigma\in(0,1]$); the labels are arbitrary. Let $\epsilon,\Delta\in(0,1/2)$ and
--   $$
--   m=m^*\bigl(c\epsilon,\ \Delta,\ c\sigma\epsilon^3/q,\ 2q\bigr)<\infty
--   $$
--   for a sufficiently small universal constant $c>0$.
--
--   **Theorem.** There is an algorithm which, given $\epsilon,\sigma,\Delta,q$ and sample access to $D$, uses at most
--   $$
--   N=d^m\exp\Bigl((qm)^{Cm}\log^{Cm}\!\Bigl(\frac{1}{\sigma\epsilon}\Bigr)\log\bigl(2+\Gamma(\mathcal F)\bigr)/\Delta^{C}\Bigr)
--   $$
--   labeled samples, runs in time polynomial in $N$, and negatively reliably learns $\mathcal F$ under $D$ with probability at least $2/3$: its hypothesis $h$ satisfies $\Pr_D[h(x)=-1,y=1]\le\epsilon$ and $\Pr_D[h(x)=1,y=-1]\le\inf_{f\in G_D}\Pr_D[f(x)=1,y=-1]+\epsilon$, with $G_D=\{f\in\mathcal F:\Pr_D[f(x)=-1,y=1]=0\}$.
--
--   **Formalization Note** The program receives $m$ and $\Gamma(\mathcal F)$ as inputs; labeled samples are points of $\mathbb R^{d+1}$.
--
--   Differences from the source:
--   - reading: bounded Gaussian surface area Γ(F) ≤ ∞ (items (1) and (3) of Definition 4.1) → Γ(F) < ∞; reason: the parenthesis refers to item (3), which requires Γ(F) < ∞
--   - reading: a class of functions with Gaussian surface area → members are Borel measurable ±1-valued functions; reason: Definition A.1 defines Γ(f) for Borel measurable Boolean functions
--   - encoding: assume m < ∞ → m∗(cϵ, Δ, cσϵ³/q, 2q) = m for a natural number m; reason: m∗ takes values in ℕ ∪ {∞}
--   - encoding: there is an algorithm that draws n samples and runs in poly(n) time → one program of the published GaussMixHH sampling RAM restricted by ArithmeticOnly, with an evaluator program computing h within the same budget; sample count ≤ n and work ≤ C·n^C on every sample stream; success on a measurable set of streams; reason: the machine model of the base mission; the paper's algorithm and time bound read in it
--   - encoding: O(·), poly(·); sufficiently small universal c → one universal natural C (and the named constants) chosen before d and every parameter; reason: a universal constant is chosen before what it is uniform over; one constant may serve several O(·) since each bound is monotone in it
--   - encoding: the parameters fixed before 'there is an algorithm' → one program, chosen after the class, given ϵ, σ, Δ, q and the class numbers m, Γ(F) in memory; reason: a finite program with rational literals cannot hard-code real parameters or class numbers; the program may depend on the class, never on the target or the distribution
--   - reading: ℝ^d → d ≥ 1; reason: the dimension is a positive integer; at d = 0 the bound d^{…} is 0
--   - encoding: a hypothesis h : ℝ^d → {±1} and Pr[h(x) ≠ y] → h(x) = 1 if the evaluator halts within the work budget with output 1, else −1; probabilities in [0, ∞] (outer measure when h is not shown measurable); reason: the output of a machine is a description; bounding the error by an outer measure only strengthens the claim
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Theorem 6.2, p.60 (PDF p.62); Definition 6.1, p.60

import Mathlib
import Definitions.Def_GaussMixHH_Machine
import Definitions.Def_GaussPart_IsSmooth
import Definitions.Def_GaussPart_ArithmeticOnly
import Definitions.Def_GaussPart_Supplement_Learner
import Definitions.Def_GaussPart_Supplement_LabeledLaw
import Definitions.Def_GaussPart_Supplement_BoolFn
import Definitions.Def_GaussPart_Supplement_SurfaceArea
import Definitions.Def_GaussPart_Supplement_PUIExponent

open MeasureTheory ProbabilityTheory

namespace GaussPart

namespace Supplement

/-- **Theorem 6.2** (Agnostic Reliable Learning under Gaussian Distribution).

I. Diakonikolas, G. Iakovidis, D. M. Kane, M. Ma, *Gaussian Partitioning for Reliable Learning of
Multi-Index Models*, arXiv:2611.05264 (copy with sha256 7e0ca6d4…), Theorem 6.2, p.60 (PDF p.62).

"Let F be a class of functions that is closed under affine restrictions and has bounded Gaussian
surface area Γ(F) ≤ ∞ (satisfies items (1) and (3) of Definition 4.1) and contains the constant
function 1. Let D be a distribution over ℝ^d × {±1} whose x-marginal is (q, σ)-smooth with respect to
N(0, I_d), where q ≥ 1 and σ ∈ (0, 1]. Let ϵ ∈ (0, 1/2) and ∆ ∈ (0, 1/2), and set
m := m∗(cϵ, ∆, cσϵ³/q, 2q) for a sufficiently small universal constant c > 0. Assume m < ∞. There is
an algorithm which, given ϵ, σ, ∆, q and sample access to D, uses at most
N = d^m exp((qm)^{O(m)} log^{O(m)}(1/(σϵ)) log(2 + Γ(F))/∆^{O(1)}) labeled samples, runs in time
polynomial in N, and negatively reliably learns F under D with probability at least 2/3."

**Formalization Note.**
* "Γ(F) ≤ ∞" is read as `Γ(F) < ∞` (item (3) of Definition 4.1); members of `F` are Borel
  measurable `±1`-valued functions. Negative reliable learning is `NegReliable` (Definition 6.1 with
  the labels interchanged); labels are arbitrary.
* `c` and one natural number `C` for every `O(·)` and `poly` come first; the program may depend on
  `F` and receives `ϵ, σ, ∆, q`, `m` and `Γ(F)`. `m < ∞` is `m∗(…) = m` for a natural `m`.
* Labeled samples, bounds on every stream, success on a measurable set of streams, the evaluated
  hypothesis: as in `theorem_4_2`. `d ≥ 1`. -/
theorem theorem_6_2 :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℕ,
    ∀ (d : ℕ), 1 ≤ d → ∀ F : Set (Vec d → ℝ), (∀ f ∈ F, IsBoolFn f) →
      ClosedUnderAffineRestr F → gsaClass F < ⊤ → (fun _ => (1 : ℝ)) ∈ F →
    ∃ (P : GaussMixHH.Program) (_ : GaussMixHH.Admissible P) (_ : ArithmeticOnly P)
      (E : GaussMixHH.Program) (_ : GaussMixHH.Admissible E) (_ : ArithmeticOnly E),
    ∀ (q σ ε Δ : ℝ), 1 ≤ q → 0 < σ → σ ≤ 1 → 0 < ε → ε < 1 / 2 → 0 < Δ → Δ < 1 / 2 →
    ∀ m : ℕ, mStar F (c * ε) Δ (c * σ * ε ^ 3 / q) (2 * q) = (m : ℕ∞) →
      let Γ : ℝ := (gsaClass F).toReal
      let N : ℝ := (d : ℝ) ^ m *
        Real.exp ((q * m) ^ (C * m) * Real.log (1 / (σ * ε)) ^ (C * m) *
          Real.log (2 + Γ) / Δ ^ C)
      let inp : List ℝ := [ε, σ, Δ, q, (m : ℝ), Γ]
      RunsWithin P (d + 1) inp N (C * N ^ C) ∧
      ∀ D : Measure (Vec d × ℝ), IsLabeledLaw D →
        IsSmooth (stdGaussian (Vec d)) (D.map Prod.fst) q σ →
        SucceedsWith P (d + 1) inp (labeledStream D) (2 / 3)
          (fun s => NegReliable F D ε (hyp E d (C * N ^ C) s)) := by sorry

end Supplement

end GaussPart
