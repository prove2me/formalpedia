-- Prove2me | Theorems.Thm_GaussPart_Supplement_theorem_4_4
-- name    : GaussPart.Supplement.theorem_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:07:26.644727+00:00
-- url     : https://prove2.me/theorems/8fd56ead-424f-4d23-81fa-9b0af0d32599
-- title:
--   Theorem 4.4 — weak learner from a Gaussian partition: error $\le 1/2-c/12$
-- statement:
--   **Setting.** Let $\mathcal F$ be $(\ell,K)$-well-behaved, $q\ge1$, $\sigma\in(0,1]$, $c\in(0,1/2)$, and let $D$ be a distribution on $\mathbb R^d\times\{\pm1\}$ whose x-marginal $Q=D_x$ is $(q,\sigma)$-smooth with respect to $\mathcal N(0,I_d)$ and with $\mathrm{opt}_D(\mathcal F)\le 1/(2(1+c))$. For a constant $C_1>1$ put
--   $$
--   \eta=\tau=\frac{c}{C_1},\quad k=\ell(c/C_1),\quad \Delta=(2Kk)^{-C_1k},\quad \delta=\frac{(c\sigma/C_1)^{3q}}{(1+\Gamma(\mathcal F))^2},
--   $$
--   and let $\mathcal P$ be a polyhedral partition that satisfies the guarantees of Theorem 3.1 for $Q$ with parameters $(q,\sigma,\eta,\delta,k,\Delta)$: at most $B$ cells, certified cells of total $Q$-mass at least $1-\eta$, each of mass at least $1/B$, diameter at most $\delta$ in $V_R$, and $k$ directional moments matching the Gaussian on $V_R^\perp$ with slack $\Delta$, where $B$ is the cell bound of Theorem 3.1.
--
--   **Theorem.** For a suitable constant $C_1>1$ there is a weak learner that, given $\mathcal P$, draws
--   $$
--   n=d^{Ck}\exp\Bigl((qKk)^{Ck}\log^{Ck}\!\Bigl(\frac{2}{c\sigma}\Bigr)\log\bigl(2+\Gamma(\mathcal F)\bigr)\Bigr)
--   $$
--   samples from $D$, runs in time $Cn^C$, and with probability at least $99\%$ outputs $h:\mathbb R^d\to\{\pm1\}$ with
--   $$
--   \Pr_{(x,y)\sim D}[h(x)\neq y]\le\frac12-\frac{c}{12}.
--   $$
--
--   Boosting this weak learner gives Theorem 4.2.
--
--   **Formalization Note** The partition guarantee is the published `IsGoodOutput` with the cell bound $B=$ `sizeBound` $C_0\ldots$ of the published goal, for every constant $C_0$; the constant $C$ may depend on $C_0$, while $C_1$ is chosen first. The learner receives $q,\sigma,c,K,k,\Gamma(\mathcal F),B$ and the cells of $\mathcal P$ (without the certification flags, which Algorithm 3 does not use).
--
--   Differences from the source:
--   - encoding: there is an algorithm that draws n samples and runs in poly(n) time → one program of the published GaussMixHH sampling RAM restricted by ArithmeticOnly, with an evaluator program computing h within the same budget; sample count ≤ n and work ≤ C·n^C on every sample stream; success on a measurable set of streams; reason: the machine model of the base mission; the paper's algorithm and time bound read in it
--   - reading: for a sufficiently large constant C1 > 1 → ∃ C1 > 1 chosen before every parameter and before the constant C₀ of Theorem 3.1's B; reason: C1 fixes the partition parameters, so it is the theorem's constant; the error analysis does not involve B
--   - encoding: a partition that satisfies the guarantees of Theorem 3.1 for Q → IsGoodOutput (D_x) k η δ Δ (sizeBound C₀ k q σ η δ Δ) L for every C₀, the constant C of n allowed to depend on C₀; reason: the cell bound B of Theorem 3.1 carries that theorem's universal constant
--   - encoding: given the partition P → the cells of P encoded in memory after q, σ, c, K, k, Γ(F), B, without the flags of G; reason: Algorithm 3 takes P, B, ℓ and τ and does not use G
--   - encoding: O(·), poly(·) → one universal natural C (and the named constants) chosen before d and every parameter; reason: a universal constant is chosen before what it is uniform over; one constant may serve several O(·) since each bound is monotone in it
--   - reading: ℝ^d → d ≥ 1; reason: the dimension is a positive integer; at d = 0 the bound d^{…} is 0
--   - encoding: a hypothesis h : ℝ^d → {±1} and Pr[h(x) ≠ y] → h(x) = 1 if the evaluator halts within the work budget with output 1, else −1; probabilities in [0, ∞] (outer measure when h is not shown measurable); reason: the output of a machine is a description; bounding the error by an outer measure only strengthens the claim
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Theorem 4.4, p.37 (PDF p.39); Algorithm 3, p.38

import Mathlib
import Definitions.Def_GaussMixHH_Machine
import Definitions.Def_GaussPart_IsSmooth
import Definitions.Def_GaussPart_ArithmeticOnly
import Definitions.Def_GaussPart_sizeBound
import Definitions.Def_GaussPart_IsGoodOutput
import Definitions.Def_GaussPart_Supplement_Learner
import Definitions.Def_GaussPart_Supplement_LabeledLaw
import Definitions.Def_GaussPart_Supplement_WellBehaved

open MeasureTheory ProbabilityTheory

namespace GaussPart

namespace Supplement

/-- **Theorem 4.4** (Weak Learner).

I. Diakonikolas, G. Iakovidis, D. M. Kane, M. Ma, *Gaussian Partitioning for Reliable Learning of
Multi-Index Models*, arXiv:2611.05264 (copy with sha256 7e0ca6d4…), Theorem 4.4, p.37 (PDF p.39).

"Fix q ≥ 1, σ ∈ (0, 1], η, δ, ∆, τ ∈ (0, 1/2), and k, d ∈ ℤ₊. Let D be a distribution on
ℝ^d × {±1} whose x-marginal Q = D_x is (q, σ)-smooth with respect to N(0, I_d). Let
F ⊆ {ℝ^d → {±1}} be a class that is (ℓ, K)-well-behaved and assume that opt_D(F) ≤ 1/(2(1 + c)),
c ∈ (0, 1/2). Let P be a partition that satisfies the guarantees of Theorem 3.1 for Q with parameters
(q, σ, η, δ, k, ∆), where η = τ = c/C1, k = ℓ(c/C1), ∆ = (2Kk)^{−C1 k}, and
δ = (cσ/C1)^{3q}/(1 + Γ(F))² for a sufficiently large constant C1 > 1. Then there is a weak learner
that, given the partition P, draws n = d^{O(k)} exp((qKk)^{O(k)} log^{O(k)}(2/(cσ)) log(2 + Γ(F)))
samples from D and runs in poly(n) time and with probability at least 99%, it outputs a hypothesis
h : ℝ^d → {±1} such that Pr_{(x,y)∼D}[h(x) ≠ y] ≤ 1/2 − c/12."

**Formalization Note.**
* `C1 > 1` is one constant chosen first (the page fixes it before the partition parameters, which it
  determines). "The guarantees of Theorem 3.1" are the published `IsGoodOutput` for `Q = D_x` at the
  printed parameters with the cell bound `B = sizeBound C₀ k q σ η δ ∆` of the published goal, for
  every constant `C₀` of that bound; the constant `C` of `n` and `poly(n) = C n^C` may depend on `C₀`.
* The learner is given the partition `P` as input (`encodePartition`, cells only: Algorithm 3 does not
  use `G`), after `q, σ, c, K, k, Γ(F), B` (the bound `B` and the degree `k = ℓ(c/C1)` are inputs of
  Algorithm 3, p.38). The program may depend on the class `F`.
* `∆` and `δ` are real powers. On the stated ranges `η, τ, δ, ∆ ∈ (0, 1/2)` hold automatically once
  `C1 ≥ 2`, as the page's "Fix … ∈ (0, 1/2)" requires.
* Labeled samples, bounds on every stream, success on a measurable set of streams and the evaluated
  hypothesis are as in `theorem_4_2`. `d ≥ 1`. -/
theorem theorem_4_4 :
    ∃ C₁ : ℝ, 1 < C₁ ∧ ∀ C₀ : ℕ, ∃ C : ℕ,
    ∀ (d : ℕ), 1 ≤ d → ∀ (ℓ : ℝ → ℕ) (K : ℕ) (F : Set (Vec d → ℝ)), IsWellBehaved ℓ K F →
    ∃ (P : GaussMixHH.Program) (_ : GaussMixHH.Admissible P) (_ : ArithmeticOnly P)
      (E : GaussMixHH.Program) (_ : GaussMixHH.Admissible E) (_ : ArithmeticOnly E),
    ∀ (q σ c : ℝ), 1 ≤ q → 0 < σ → σ ≤ 1 → 0 < c → c < 1 / 2 →
    ∀ (D : Measure (Vec d × ℝ)), IsLabeledLaw D →
      IsSmooth (stdGaussian (Vec d)) (D.map Prod.fst) q σ →
      opt D F ≤ ENNReal.ofReal (1 / (2 * (1 + c))) →
      let Γ : ℝ := (gsaClass F).toReal
      let k : ℕ := ℓ (c / C₁)
      let η : ℝ := c / C₁
      let Δ : ℝ := (2 * (K : ℝ) * k) ^ (-(C₁ * k))
      let δ : ℝ := (c * σ / C₁) ^ (3 * q) / (1 + Γ) ^ 2
      let B : ℝ := sizeBound C₀ k q σ η δ Δ
      ∀ L : List (Cell d × Bool), IsGoodOutput (D.map Prod.fst) k η δ Δ B L →
        let n : ℝ := (d : ℝ) ^ (C * k) *
          Real.exp ((q * K * k) ^ (C * k) * Real.log (2 / (c * σ)) ^ (C * k) * Real.log (2 + Γ))
        let inp : List ℝ := [q, σ, c, (K : ℝ), (k : ℝ), Γ, B] ++ encodePartition (L.map Prod.fst)
        RunsWithin P (d + 1) inp n (C * n ^ C) ∧
        SucceedsWith P (d + 1) inp (labeledStream D) (99 / 100) (fun s =>
          err D (hyp E d (C * n ^ C) s) ≤ ENNReal.ofReal (1 / 2 - c / 12)) := by sorry

end Supplement

end GaussPart
