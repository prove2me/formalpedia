-- Prove2me | Theorems.Thm_MaskingHardness_theorem_1_9
-- name    : MaskingHardness.theorem_1_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:52:27.783009+00:00
-- url     : https://prove2.me/theorems/ca2aa4c3-28ec-4209-b9e5-72c9b7d222a7
-- title:
--   Theorem 1.9 — hardness vs fidelity: least $\ell_1$-regularized loss over $\mathrm{span}(\mathcal C)$ = highest fidelity of a $(\mathcal C,\varepsilon)$-masking channel
-- statement:
--   Let $\mathcal X$ be finite, $\mathcal Y=[k]$, $\mathcal D$ a distribution over $(x,y)\in\mathcal X\times\mathcal Y$, $\mathcal C\subseteq\{\mathcal X\to\mathbb R^k\}$ finite, $g:\mathcal Y\times\mathbb R^k\to\mathbb R$ and $h:\mathcal Y\times\Delta_k\to\overline{\mathbb R}$ convex–concave conjugates, and $\varepsilon\ge0$. Then
--
--   1. the least regularized loss equals the highest fidelity of a masking channel, and the latter is attained:
--
--   $$
--   \inf_{\lambda\in\mathbb R^{\mathcal C}}\mathbb E\bigl[g(y,\pi(c_\lambda(x)))\bigr]+\varepsilon\|\lambda\|_1=\max_{W:\mathcal X\to\Delta_k^k}\mathbb E\bigl[h(y,W(x)y)\bigr]\quad\text{s.t. } W \text{ is } (\mathcal C,\varepsilon)\text{-masking};
--   $$
--
--   2. (footnote 8) if $\varepsilon>0$ and $g(\cdot,\pi(\cdot))$ is bounded below, the infimum on the left is attained, i.e. it is a minimum.
--
--   Here $\pi$ is the centering map, $c_\lambda=\sum_i\lambda_ic_i$, $\|\lambda\|_1=\sum_i|\lambda_i|$, and $W(x)y$ is the column of the column-stochastic matrix $W(x)$ selected by the label $y$. The left side measures how hard it is to learn $\mathcal D$ with $\mathrm{span}(\mathcal C)$; the right side is the highest fidelity of a channel that makes the labels look uniform to $\mathcal C$. The theorem is the paper's multiclass generalization of the hardcore lemma.
--
--   **Formalization Note** The infimum is taken in `EReal` (it may be $-\infty$), "max" is `IsGreatest` of the set of fidelities of masking channels, "minimum" is `IsLeast` of the range of the regularized loss. $h$ is a function on $\mathbb R^k$ equal to $-\infty$ off $\Delta_k$; $C=\emptyset$ and $\varepsilon=0$ are included.
--
--   Differences from the source:
--   - generalization: a finite set C ⊆ {X → ℝᵏ} → a finite indexed family c : ι → X → ℝᵏ, repetitions allowed; reason: the paper's set C is the family indexed by its own elements (ι = C, c = inclusion), so the statement specializes to the source's
--   - encoding: a distribution D over X × Y → weights D x y ≥ 0 summing to 1 (IsDist); expectations are the weighted finite sums; reason: finite sets; same distributions, zero-probability pairs allowed
--   - encoding: h : Y × Δ_k → ℝ̄, judged by its extension by −∞ off Δ_k (Definition 2.2) → h : Fin k → ℝᵏ → EReal with h y z = ⊥ for z ∉ Δ_k; reason: the extension prescribed by Definition 2.2; same functions on Δ_k
--   - encoding: convex–concave conjugates (Definition 2.6: closed proper convex g, closed proper concave h, conjugacy formulas) → IsConvConcConj: the two conjugacy formulas plus properness of g and h; reason: closedness and (con)vexity follow from the formulas (suprema/infima of affine functions); equivalent predicates
--   - encoding: Y = [k], labels identified with e₁,…,e_k; W(x)y the column of W(x) selected by y → labels Fin k; W(x)y is the column fun i => W x i y; reason: Lean convention; same channels
--   - encoding: E[v(x, y)] for an ℝ̄-valued v → ∑ₓ ∑_y D x y · v x y in EReal, with 0 · (±∞) = 0; reason: pairs of probability zero do not contribute, as in the paper's treatment of D-null pairs (footnotes 17, 18)
--   - encoding: ‖λ‖₁ → ∑ i, |λ i|; reason: Mathlib's norm on ι → ℝ is the sup norm; this is the ℓ₁ norm
--   - encoding: inf … = max_W … s.t. W is (C, ε)-masking → IsGreatest of {channelFidelity D h W : W masking} at the EReal infimum of the real objective; reason: equality with a maximum means the supremum equals the infimum and is attained
--   - encoding: footnote 8: when ε ≠ 0 and g(·, π(·)) is bounded below, the infimum can be replaced with a minimum → 0 < ε → (∃ v, ∀ y a, v ≤ g y (centered a)) → ∃ λ₀, IsLeast (range of the objective) (objective λ₀); reason: ε ≥ 0, so ε ≠ 0 is ε > 0; a minimum is an attained infimum
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Theorem 1.9 with footnote 8, p.6 (PDF p.8); restated with footnote 19, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_MaskingHardness_IsConvConcConj
import Definitions.Def_MaskingHardness_IsDist
import Definitions.Def_MaskingHardness_centered
import Definitions.Def_MaskingHardness_IsMaskingChannel
import Definitions.Def_MaskingHardness_lossObjective
import Definitions.Def_MaskingHardness_channelFidelity

namespace MaskingHardness

/-- **Theorem 1.9** (Hardness vs Fidelity) (Gopalan–Prabhakaran–Tankala, *Universal Hardness From
Masking Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d, Theorem 1.9 with
footnote 8, printed p.6 = PDF p.8; restated with footnote 19, printed p.22 = PDF p.24).

For all finite `X`, `Y = [k]`, distributions `D` over `(x, y) ∈ X × Y`, finite
`C ⊆ {X → ℝᵏ}`, convex–concave conjugates `g : Y × ℝᵏ → ℝ`, `h : Y × Δ_k → ℝ̄`, and `ε ≥ 0`:
(i) `inf_{λ ∈ ℝ^C} E[g(y, π(c_λ(x)))] + ε‖λ‖₁ = max_{W : X → Δ_k^k} E[h(y, W(x)y)]` subject to
`W` being `(C, ε)`-masking, the maximum being attained;
(ii) (footnote 8) when `ε ≠ 0` and `g(·, π(·))` is bounded below, the infimum on the left-hand
side is a minimum.

**Formalization Note** ℝ̄ is `EReal`; the infimum in (i) is taken in `EReal` (it may be `−∞`);
"max" is `IsGreatest` of the set of fidelities of masking channels, "minimum" is `IsLeast`; `h`
is given on `ℝᵏ` and equals `−∞` off `Δ_k`; `C` is a finite indexed family; `W(x)y` is the
`y`-th column of `W(x)`. -/
theorem theorem_1_9 {X ι : Type*} [Fintype X] [Fintype ι] {k : ℕ}
    (D : X → Fin k → ℝ) (hD : IsDist D) (c : ι → X → Fin k → ℝ)
    (g : Fin k → (Fin k → ℝ) → ℝ) (h : Fin k → (Fin k → ℝ) → EReal)
    (hdom : ∀ y z, z ∉ stdSimplex ℝ (Fin k) → h y z = ⊥)
    (hgh : ∀ y, IsConvConcConj (fun a => ((g y a : ℝ) : EReal)) (h y))
    (ε : ℝ) (hε : 0 ≤ ε) :
    IsGreatest
        {v : EReal | ∃ W : X → Matrix (Fin k) (Fin k) ℝ,
          IsMaskingChannel D c ε W ∧ v = channelFidelity D h W}
        (⨅ lam : ι → ℝ, ((lossObjective D c g ε lam : ℝ) : EReal)) ∧
      (0 < ε → (∃ v : ℝ, ∀ y a, v ≤ g y (centered a)) →
        ∃ lam₀ : ι → ℝ, IsLeast (Set.range (lossObjective D c g ε)) (lossObjective D c g ε lam₀)) := by sorry

end MaskingHardness
