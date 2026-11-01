-- Prove2me | Theorems.Thm_FracMPGA_lemma_4_7
-- name    : FracMPGA.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:41:42.639288+00:00
-- url     : https://prove2.me/theorems/2012e1f0-df93-41c5-ad6b-61011164561f
-- title:
--   Lemma 4.7 — $\eta$ is Lipschitz on $\mathcal X\times\mathcal Y$ and $Q$ is continuous on $\mathcal S$
-- statement:
--   Suppose Assumption 2 holds and let $\mathcal Y,\mathcal S$ be built from a bound $\bar g_{\mathcal X}$ and $\underline\alpha>0$. Then $\eta(x,y)=\langle x,y\rangle-g^*(y)$ is finite and Lipschitz continuous on $\mathcal X\times\mathcal Y$: there is $L$ with
--   $$
--   |\eta(x_1,y_1)-\eta(x_2,y_2)|\le L\,\|(x_1,y_1)-(x_2,y_2)\|_2\qquad\text{for }x_1,x_2\in\mathcal X,\ y_1,y_2\in\mathcal Y,
--   $$
--   and therefore the objective $Q$ is continuous on $\mathcal S$.
--
--   Continuity of $Q$ on $\mathcal S$ replaces lower semicontinuity, which $Q$ lacks, in the convergence analysis.
--
--   Differences from the source:
--   - encoding: ℝⁿ and ℝⁿ × ℝⁿ with the Euclidean norm and inner product → EuclideanSpace ℝ (Fin n) (Vec n) and WithLp 2 (Vec n × Vec n) (Pair n); reason: Lean convention; the same norms and inner products
--   - encoding: h : ℝⁿ → (−∞, +∞] proper lower semicontinuous, locally Lipschitz differentiable on Ω → h : Vec n → ℝ, differentiable on Ω with gradient locally Lipschitz relative to Ω; reason: h enters only through ζ = f + h and ∇h on the open set Ω; its values off Ω change no value of F or Q, no critical point and no accepted step (a trial point outside Ω fails the line-search test, since η ≤ g = 0 there and ζ ≥ 0 on dom f)
--   - encoding: subvectors x₁, …, x_N partitioning the coordinates of x, blocks i ∈ ℕ_N = {1, …, N} → a surjective blk : Fin n → Fin N with block spaces EuclideanSpace ℝ {j // blk j = i}; paper block i is index i − 1; reason: Lean convention; the same partitions into nonempty blocks
--   - encoding: extended values in (−∞, +∞] and [−∞, +∞) → EReal, with the real quotient on the finite branch of F and Q; reason: Lean convention; the same values
--   - reading: ḡ_X > 0 given by Remark 1(i) → any gbar > 0 with g ≤ gbar on X, a parameter of Y and S; reason: Remark 1(i) only asserts that such a bound exists and every result holds for each one; η ≤ g is Fenchel–Young, not a hypothesis
--   - encoding: x^(0) of Assumption 2 (the input of Step 0, x^(0) ∈ dom(F)) → a point x0 with hypothesis F x0 ≠ ⊤; reason: Step 0 of Algorithm 1 requires x^(0) ∈ dom(F), and Assumption 2 refers to that point
--   - encoding: η : ℝⁿ × ℝⁿ → [−∞, +∞) is Lipschitz continuous on X × Y → η is finite on X × Y and its real values satisfy |η p − η q| ≤ L‖p − q‖₂ there; reason: a Lipschitz bound for an extended-valued function presupposes finite values
-- source:
--   Zhou, Zhang, Li, An equivalent reformulation and multi-proximity gradient algorithms for a class of nonsmooth fractional programming, arXiv:2311.00957v2, §4, p.18, Lemma 4.7

import Mathlib
import Definitions.Def_FracMPGA_liftedRatio
import Definitions.Def_FracMPGA_Problem
import Definitions.Def_FracMPGA_Assumption1
import Definitions.Def_FracMPGA_setS

namespace FracMPGA

/-- **Lemma 4.7** of Zhou, Zhang, Li, arXiv:2311.00957v2, p.18: suppose that Assumption 2 holds.
Let `η : ℝⁿ × ℝⁿ → [−∞, +∞)` be `η(x, y) = ⟨x, y⟩ − g*(y)`. Then `η` is Lipschitz continuous on
`X × Y`, and thus the objective `Q` given by (9) is continuous on `S`.

**Formalization Note** Assumption 1 is `hA1`; Assumption 2 is `IsCompact (P.levelX x0)` with
`x0 = x⁽⁰⁾ ∈ dom(F)`; `Y` and `S` are built from a bound `gbar` of Remark 1(i) and `α̲ = αlo > 0`.
"Lipschitz continuous on `X × Y`" is stated as: `η` is finite on `X × Y`, and for some `L` its
real values satisfy `|η(x₁, y₁) − η(x₂, y₂)| ≤ L ‖(x₁, y₁) − (x₂, y₂)‖₂` there (Euclidean norm on
`ℝⁿ × ℝⁿ`). Continuity of the `EReal`-valued `Q` on `S` is `ContinuousOn P.Qp (P.setS …)`. -/
theorem lemma_4_7 {n N : ℕ} (P : Problem n N) (hA1 : Assumption1 P) (x0 : Vec n)
    (hx0 : P.F x0 ≠ ⊤) (hA2 : IsCompact (P.levelX x0)) (gbar : ℝ) (hgbar : 0 < gbar)
    (hgX : ∀ z ∈ P.levelX x0, P.g z ≤ gbar) (αlo : ℝ) (hαlo : 0 < αlo) :
    (∀ x ∈ P.levelX x0, ∀ y ∈ P.setY x0 gbar αlo, P.eta x y ≠ ⊥ ∧ P.eta x y ≠ ⊤) ∧
    (∃ L : ℝ, ∀ x₁ ∈ P.levelX x0, ∀ y₁ ∈ P.setY x0 gbar αlo,
      ∀ x₂ ∈ P.levelX x0, ∀ y₂ ∈ P.setY x0 gbar αlo,
        |(P.eta x₁ y₁).toReal - (P.eta x₂ y₂).toReal| ≤ L * ‖pair x₁ y₁ - pair x₂ y₂‖) ∧
    ContinuousOn P.Qp (P.setS x0 gbar αlo) := by sorry

end FracMPGA
