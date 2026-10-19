-- Prove2me | Theorems.Thm_OAI_WeakPinned_arithmetic_balanced_length
-- name    : OAI.WeakPinned.arithmetic_balanced_length
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T01:03:05.214126+00:00
-- url     : https://prove2.me/theorems/c4b045ee-4efe-4f2c-a1bb-f6d183656492
-- title:
--   If the overlap scales of prepared arithmetic fiber graphs tend to infinity, a fixed fraction of the cell mass sits on balanced cells (OpenAI weak pinned distances)
-- statement:
--   **The setting.** For each $j \in \mathbb N$ let $V_j$ and $I_j$ be finite types, $N_j = |V_j|$, and let $K_j$ be a number field. Let $G_j$ be a fiber graph on $V_j$ (`Core.Fibers`). Each index $e \in I_j$ has a source $\sigma(e) \in V_j$ and a set of targets $B_e \subseteq V_j$ not containing $\sigma(e)$, and indices with the same source have disjoint target sets. The edges of $G_j$ are the pairs $(\sigma(e), y)$ with $y \in B_e$. Let $Z^1_j, Z^2_j : V_j \to K_j$ be injective. Let $\theta > 0$, $0 < \gamma < 1$ and $c < \gamma$ be reals, and let $\eta_j$ be reals with $0 \le \eta_j \le \theta/2$ and $\eta_j \to 0$. Assume:
--
--   - $N_j \to \infty$;
--   - each $G_j$ is a `PreparedGraph` with parameters $\theta, \gamma, c, \eta_j$. With $N = N_j$ and $\lambda = 1/\log N$, this means:
--     - $N \ge 2$;
--     - the number of edges lies between $(\theta - \eta_j) N(N-1)$ and $(\theta + \eta_j/8) N(N-1)$;
--     - every vertex meets at least $2(\theta - \eta_j)(N-1)$ edges;
--     - every target set has more than $N^\gamma$ elements;
--     - for every vertex set $D$, the heavy count (the sum of $|B_e \cap D|$ over the indices $e$ with $\sigma(e) \in D$ and $|B_e \cap D| \ge \lambda |B_e|$) is at most $(\theta + \eta_j)|D|(|D|-1)$, and at most $\eta_j |D|(|D|-1)$ when $|D| \le N^{1-c}$;
--   - the fibers are arithmetic: there are $t_j(e) \in K_j$ with $(Z^1_j\sigma(e) - Z^1_j y)(Z^2_j\sigma(e) - Z^2_j y) = t_j(e)$ for all $e$ and all $y \in B_e$.
--
--   **The quantities.** For a cell $C \subseteq V_j$, $m_j(C)$ (`totalMass`) is the sum of the arithmetic cell masses `cellMass` of $C$ for $Z^1_j$ and for $Z^2_j$. The cell mass of $C$ adds up, over the places of $K_j$, the scale-integrated multiplicity with which $C$ occurs as a cluster in the hierarchy of the points $Z(x)$ at that place. Archimedean places are averaged over random grids and weighted by `archWeight`; the finitely many bad finite places are weighted by $1/[K_j : \mathbb Q]$. The overlap scale is $W_j = \sum_C m_j(C)\, \frac{|C|(|C|-1)}{N_j(N_j-1)}$ (`overlapScale`). For $\delta \in \mathbb R$, the tent function is $\tau_\delta(u) = \max(0, \min(u - \delta,\ 1 - \delta - u))$ (`Cuts.tent`).
--
--   **The statement.** Assume moreover $W_j \to \infty$. Then there is a $\delta$ with $0 < \delta \le 1/8$ such that, for all large $j$,
--   $$\frac{\delta}{4}\, W_j \;\le\; \sum_{C \subseteq V_j} m_j(C)\, \tau_\delta\!\left(\frac{|C|}{N_j}\right).$$
--
--   Lean: `OAI.WeakPinned.arithmetic_balanced_length`, OpenAI's lemma of that name (in `lean/OAI/Geometry/PinnedDistances/UnboundedContradiction.lean`); the right-hand side is `weightedIntegral (totalMass …) (fun C => tent δ (cellProb Finset.univ C))`. `Core.Fibers`, `PreparedGraph`, `overlapScale`, `totalMass`, `Variance.weightedIntegral`, `Variance.cellProb` and `Cuts.tent` come from the definitions bundle `OAIQWWP000` of this split.
-- source:
--   OpenAI, The weak pinned planar distance theorem, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 167; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-weak-pinned-planar-distance-theorem-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/PinnedDistances/UnboundedContradiction.lean (declaration OAI.WeakPinned.arithmetic_balanced_length)

import Mathlib
import Definitions.Def_OAIQWWP000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12
universe u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23

section

namespace WeakPinned
open Filter Variance Global Cuts SmallFiber
open scoped Topology BigOperators
variable {V : ℕ → Type u6} {I : ℕ → Type u7} {K : ℕ → Type u8} [∀ j, Fintype (V j)] [∀ j, Fintype (I j)] [∀ j, DecidableEq (V j)]
  [∀ j, Field (K j)] [∀ j, NumberField (K j)]
variable (G : ∀ j, Core.Fibers (V j) (I j)) (θ γ c : ℝ) (η : ℕ → ℝ)
  (Z₁ Z₂ : ∀ j, V j → K j) (h₁ : ∀ j, Function.Injective (Z₁ j)) (h₂ : ∀ j, Function.Injective (Z₂ j))

theorem arithmetic_balanced_length (hθ : 0<θ) (hγ : 0<γ) (hγ1 : γ<1) (hcγ : c<γ)
    (hn : Tendsto (fun j => (Fintype.card (V j):ℝ)) atTop atTop)
    (hη : Tendsto η atTop (𝓝 0)) (hη0 : ∀ j, 0≤η j) (hηb : ∀ j, η j≤θ/2)
    (hG : ∀ j, PreparedGraph (V j) (I j) (G j) θ γ c (η j))
    (t : ∀ j, I j → K j) (ht : ∀ j e y, y ∈ (G j).targets e →
      (Z₁ j ((G j).source e)-Z₁ j y)*(Z₂ j ((G j).source e)-Z₂ j y)=t j e)
    (hWtop : Tendsto (fun j => overlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)) atTop atTop) :
    ∃ δ : ℝ, 0<δ ∧ δ≤1/8 ∧ ∀ᶠ j in atTop,
      (δ/4)*overlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j) ≤
        weightedIntegral (totalMass (Z₁ j) (Z₂ j) (h₁ j) (h₂ j))
          (fun C => tent δ (cellProb Finset.univ C)) := by
  sorry
end WeakPinned
end

end OAI
end
