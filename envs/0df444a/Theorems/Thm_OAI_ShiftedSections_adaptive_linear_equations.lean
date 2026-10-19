-- Prove2me | Theorems.Thm_OAI_ShiftedSections_adaptive_linear_equations
-- name    : OAI.ShiftedSections.adaptive_linear_equations
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T19:21:22.546785+00:00
-- url     : https://prove2.me/theorems/c16112ed-e0cb-49f6-86c3-5a22385dbc49
-- title:
--   Signs with adaptive shifts: a symmetric convex body with large compressed heat-operator norms contains a signed point solving prescribed triangular linear equations
-- statement:
--   Let $\iota$ be a finite type with decidable equality, and let $V = \mathbb R^\iota$ with the Euclidean norm (`Coeff`, which is `EuclideanSpace ℝ ι`), Lebesgue measure, and standard basis vectors $e_k$ (`EuclideanSpace.single k 1`).
--
--   **The heat-operator bound.** For a measurable set $D \subseteq V$ and a real number $c$, `HeatL2.Diagonal.Bound D hD c` (from the definitions bundle `OAIQWESB000`) means: for every weight vector $v \in [0,\infty)^\iota$ (`v : ι → ℝ≥0`),
--   $$e^{-(c/2)\sum_i v_i} \;\le\; \bigl\|\, P_D\, T_v\, P_D \,\bigr\|,$$
--   where the norm is the operator norm on $L^2(V; \mathbb C)$ with Lebesgue measure, $P_D$ is multiplication by the indicator of $D$ (`HeatL2.mask`), and $T_v$ is the Fourier multiplier with symbol $\xi \mapsto \exp\bigl(-\tfrac12 \sum_i v_i (2\pi \xi_i)^2\bigr)$ (`HeatL2.heat (GaussianKernel.symbol v)`, defined with Mathlib's $L^2$ Fourier transform `Lp.fourierTransformₗᵢ`), that is, convolution with the centered Gaussian density of covariance $\mathrm{diag}(v)$. The composite $P_D T_v P_D$ is `HeatL2.compressedHeat`.
--
--   **Good bodies.** `ShiftedSections.Good K` (from the bundle `OAIQWESB000`) means that $K \subseteq V$ is nonempty, open, bounded (`Bornology.IsBounded`), convex, symmetric about the origin ($-x \in K$ for $x \in K$), and satisfies `Bound K _ (1/10000)`, the bound above with $c = 1/10000$.
--
--   **Statement.** Let $n$ be a natural number and $j : \{0, \dots, n-1\} \to \iota$ an injective map (`j : Fin n → ι`, `Function.Injective j`). For each $i < n$ let $m_i : V \to \mathbb R$ be a continuous linear functional (`m : Fin n → Coeff →L[ℝ] ℝ`) such that $m_i(e_{j(l)}) = 0$ whenever $i \le l$. Let $K$ be `Good`, and suppose $|m_i(x)| < 1/4$ for every $x \in K$ and every $i$. Then there are signs $\varepsilon_i \in \{-1, 1\}$ and a point $x \in K$ such that
--   $$x_k = 0 \text{ for every } k \notin j(\{0,\dots,n-1\}), \qquad x_{j(i)} = m_i(x) + \varepsilon_i \text{ for every } i < n.$$
--
--   Because $m_i$ only reads the coordinates $x_{j(0)}, \dots, x_{j(i-1)}$, the equations determine $x$ step by step from the signs: this is the sign recursion $x^{(i)} = x^{(i-1)} + \bigl(q_i + \varepsilon_i\bigr) e_{j(i)}$ with shifts $q_i = m_i(x^{(i-1)})$, $|q_i| < 1/4$, of Proposition 2.1 of OpenAI's paper. There the hypothesis on $K$ is a Dirichlet-energy bound; the Lean statement uses the heat-operator bound above instead.
--
--   Lean: `OAI.ShiftedSections.adaptive_linear_equations`, OpenAI's lemma of that name (in `lean/OAI/Analysis/Steinitz/SigningData.lean`). `Coeff`, `Good`, `HeatL2.Diagonal.Bound`, `HeatL2.compressedHeat`, `HeatL2.heat`, `HeatL2.mask`, `HeatL2.spectralOp` and `GaussianKernel.symbol` come from the definitions bundle `OAIQWESB000` of this split.
-- source:
--   The shifted-section method of S. Guo, E. X. Fang and J. Lu, Vector balancing via directional total variation, arXiv:2609.11189 (2026), Proposition 2.2 and Lemmas 3.3–3.4 and 4.1–4.3, as adapted in OpenAI, The Euclidean Steinitz–Bergström theorem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 097; Proposition 2.1 and Section 3; Apache License 2.0), which also gives the proof and the Lean code; Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Steinitz/SigningData.lean (declaration OAI.ShiftedSections.adaptive_linear_equations)

import Mathlib
import Definitions.Def_OAIQWESB000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Set
namespace ShiftedSections
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma adaptive_linear_equations {n : ℕ} (j : Fin n → ι) (hj : Function.Injective j)
    (m : Fin n → Coeff (ι := ι) →L[ℝ] ℝ)
    (hm : ∀ i l : Fin n,i≤l → m i (EuclideanSpace.single (j l) 1)=0)
    {K : Set (Coeff (ι := ι))} (hK : Good K) (hslab : ∀ x∈K,∀ i,|m i x|<1/4) :
    ∃ ε : Fin n → ℝ,∃ x : Coeff (ι := ι),
      (∀ i,ε i = -1 ∨ ε i=1) ∧ x∈K ∧
      (∀ k,(∀ i,k≠j i) → x k=0) ∧ (∀ i,x (j i)=m i x+ε i) := by
  sorry

end ShiftedSections

end

end OAI
end
