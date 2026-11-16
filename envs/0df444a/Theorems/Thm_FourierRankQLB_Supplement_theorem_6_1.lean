-- Prove2me | Theorems.Thm_FourierRankQLB_Supplement_theorem_6_1
-- name    : FourierRankQLB.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T23:21:49.494711+00:00
-- url     : https://prove2.me/theorems/4cf06e36-27bd-423a-b966-f742a2b07156
-- title:
--   Theorem 6.1 — minimizing 1-strongly convex $\kappa$-smooth quadratics to accuracy $1/200$ needs $\min\{\sqrt\kappa, n\}/10^5$ gradient phase queries
-- statement:
--   Let $n \ge 1$ and $\kappa \ge 1$, and put
--
--   $$
--   q := \min\{\sqrt\kappa,\, n\}, \qquad \varepsilon_{\mathrm{quad}} := \frac1{200}.
--   $$
--
--   For a differentiable $f:\mathbb R^n\to\mathbb R$, the ideal gradient phase oracle (58) acts on labels $(x,u)\in\mathbb R^n\times\mathbb R^n$ by $(G_f\psi)(x,u) = e^{i u^\top\nabla f(x)}\psi(x,u)$; one application of $G_f$ or $G_f^{-1}$ is one gradient query.
--
--   **Theorem.** There is a family $\mathcal F_{n,\kappa}$ of quadratic functions on $\mathbb R^n$, each 1-strongly convex and κ-smooth ($I \preceq \nabla^2 f \preceq \kappa I$), such that every quantum algorithm which, for every $f \in \mathcal F_{n,\kappa}$, returns $\hat x$ with
--
--   $$
--   f(\hat x) \le \min_{x\in\mathbb R^n} f(x) + \varepsilon_{\mathrm{quad}} \qquad (69)
--   $$
--
--   with probability at least $2/3$ makes at least
--
--   $$
--   \frac{q}{10^5} \qquad (70)
--   $$
--
--   gradient phase queries in the worst case.
--
--   The bound matches, up to the factor $\log\kappa$ of accelerated gradient descent and the $O(n)$ of conjugate gradients, the $\min\{\sqrt\kappa, n\}$ dependence of the known upper bounds, in the ideal quantum gradient-query model.
--
--   **Formalization Note** The family is existential and depends only on $n$ and $\kappa$; it is chosen before the algorithm and its label space. The algorithm is a $T$-query algorithm (15) on $L^2(Y,\nu)\otimes W$ with a POVM on $\mathbb R^n$; its circuit, slot directions, labels and POVM are fixed before $f$.
--
--   Differences from the source:
--
--   - generalization: the register L²(ℝⁿ × ℝⁿ) (Remark 3.6 / end of §6.1: also any finite label set with counting measure), with a workspace → L²(Y, ν) ⊗ W = L²(Y, ν; W) for any σ-finite (Y, ν), measurable labels ι : Y → ℝⁿ × ℝⁿ and any complex Hilbert space W; reason: covers more algorithms; Y = ℝⁿ × ℝⁿ with Lebesgue measure and ι = id gives L²(ℝⁿ × ℝⁿ), and a finite label set with counting measure gives the remark's finite registers
--   - encoding: one application of G_f or G_f^{-1} counts as one gradient query; "in the worst case" → a direction vector inv : Fin T → Bool fixed with the algorithm, and the bound on the number T of slots; reason: Lean representation of the paper's query model; the number of slots is the worst-case query count
--   - encoding: f(x̂) ≤ min_{x ∈ ℝⁿ} f(x) + ε → x̂ ∈ {x | ∀ z, f x ≤ f z + ε}; reason: equivalent, since every 1-strongly convex quadratic attains its minimum
--   - encoding: a quadratic function, 1-strongly convex and κ-smooth → IsSCSmoothQuadratic κ f: f = ½xᵀHx + bᵀx + c with H symmetric, (H − I) and (κI − H) positive semidefinite; reason: the paper's own definition on p.33 (I ⪯ H ⪯ κI)
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Theorem 6.1, p.35 (oracle Eq. (58), p.33; finite labels, end of §6.1, p.34)

import Mathlib
import Definitions.Def_FourierRankQLB_Supplement_gradPhaseOracle
import Definitions.Def_FourierRankQLB_Supplement_dirOracles
import Definitions.Def_FourierRankQLB_Supplement_IsSCSmoothQuadratic
import Definitions.Def_FourierRankQLB_QueryAlg_outcomeProb

open MeasureTheory

namespace FourierRankQLB

namespace Supplement

/-- Theorem 6.1 (Linear gradient-query lower bound). Let `n ≥ 1` and `κ ≥ 1`, and put
`q := min{√κ, n}` and `ε_quad := 1/200`. There is an explicit family `F_{n,κ}` of quadratic
functions on `ℝⁿ`, each 1-strongly convex and κ-smooth, such that any quantum algorithm which, for
every `f ∈ F_{n,κ}`, returns `x̂` satisfying `f(x̂) ≤ min_{x ∈ ℝⁿ} f(x) + ε_quad` (69) with probability
at least `2/3` makes at least `q/10⁵` (70) queries to the gradient phase oracle (58) in the worst case.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Theorem 6.1, p. 35 (oracle: Eq. (58), p. 33; finite label sets: end of §6.1, p. 34).

**Formalization Note.** The family depends only on `n` and `κ` and is chosen before the algorithm.
The algorithm is a `T`-query algorithm (15) on `L²(Y, ν) ⊗ W` for any σ-finite label space whose
labels `y` represent query pairs `ι y = (x, u) ∈ ℝⁿ × ℝⁿ` (the paper's `L²(ℝⁿ × ℝⁿ)` is `Y = ℝⁿ × ℝⁿ`,
Lebesgue measure, `ι = id`) and any workspace `W`; slot `j` applies `G_f` or `G_f⁻¹` according to
`inv j`, and its POVM has outcomes in `ℝⁿ`. The success event (69) is written
`∀ z, f(x̂) ≤ f(z) + ε_quad`, which is (69) because a strongly convex quadratic attains its minimum.
The query count is the number `T` of oracle slots. -/
theorem theorem_6_1 {n : ℕ} (hn : 1 ≤ n) {κ : ℝ} (hκ : 1 ≤ κ) :
    ∃ F : Set (Ambient n → ℝ), (∀ f ∈ F, IsSCSmoothQuadratic κ f) ∧
      ∀ {Y : Type} [MeasurableSpace Y] (ν : Measure Y) [SigmaFinite ν]
        (ι : Y → Ambient n × Ambient n) (hι : Measurable ι)
        {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
        (A : QueryAlg (Lp W 2 ν) (Ambient n)) (inv : Fin A.T → Bool),
        (∀ f ∈ F, 2 / 3 ≤ A.outcomeProb (dirOracles (gradPhaseOracle ν W ι hι f) inv)
          {x | ∀ z, f x ≤ f z + 1 / 200}) →
        min (√κ) (n : ℝ) / 10 ^ 5 ≤ A.T := by sorry

end Supplement

end FourierRankQLB
