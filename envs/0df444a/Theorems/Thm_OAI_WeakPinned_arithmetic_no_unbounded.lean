-- Prove2me | Theorems.Thm_OAI_WeakPinned_arithmetic_no_unbounded
-- name    : OAI.WeakPinned.arithmetic_no_unbounded
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T01:03:01.770908+00:00
-- url     : https://prove2.me/theorems/38fb56b7-be7e-4679-88c7-2a359fa4ee51
-- title:
--   No sequence of prepared fiber graphs with arithmetic fibers has overlap scales tending to infinity (OpenAI weak pinned distances, unbounded case)
-- statement:
--   **The setting.** For each $j \in \mathbb N$ let $V_j$ and $I_j$ be finite types, $N_j = |V_j|$, and let $K_j$ be a number field. Let $G_j$ be a fiber graph on $V_j$ (`Core.Fibers`). Each index $e \in I_j$ has a source $\sigma(e) \in V_j$ and a set of targets $B_e \subseteq V_j$ not containing $\sigma(e)$, and indices with the same source have disjoint target sets. The edges of $G_j$ are the pairs $(\sigma(e), y)$ with $y \in B_e$. Let $Z^1_j, Z^2_j : V_j \to K_j$ be injective. Let $\theta > 0$, $0 < \gamma < 1$ and $0 < c < \gamma$ be reals, and let $\eta_j$ be reals with $0 \le \eta_j \le \theta/2$ and $\eta_j \to 0$. Assume:
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
--   **The overlap scale.** For a cell $C \subseteq V_j$, $m_j(C)$ (`totalMass`) is the sum of the arithmetic cell masses `cellMass` of $C$ for $Z^1_j$ and for $Z^2_j$. The cell mass of $C$ adds up, over the places of $K_j$, the scale-integrated multiplicity with which $C$ occurs as a cluster in the hierarchy of the points $Z(x)$ at that place. Archimedean places are averaged over random grids and weighted by `archWeight`; the finitely many bad finite places are weighted by $1/[K_j : \mathbb Q]$. The overlap scale is
--   $$W_j = \sum_{C \subseteq V_j} m_j(C)\, \frac{|C|(|C|-1)}{N_j(N_j-1)} \qquad (\texttt{overlapScale}).$$
--
--   **The statement.** These assumptions together with $W_j \to \infty$ are contradictory. The number fields $K_j$ may vary with $j$, with no bound on their degrees.
--
--   Lean: `OAI.WeakPinned.arithmetic_no_unbounded`, OpenAI's lemma of that name (in `lean/OAI/Geometry/PinnedDistances/UnboundedContradiction.lean`), with conclusion `False`. `Core.Fibers`, `PreparedGraph`, `overlapScale` and `totalMass` come from the definitions bundle `OAIQWWP000` of this split.
-- source:
--   OpenAI, The weak pinned planar distance theorem, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 167; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-weak-pinned-planar-distance-theorem-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/PinnedDistances/UnboundedContradiction.lean (declaration OAI.WeakPinned.arithmetic_no_unbounded)

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
noncomputable section
noncomputable section
noncomputable section
namespace WeakPinned
open Filter Variance Global Cuts
open scoped Topology BigOperators

variable {V : ℕ → Type u21} {I : ℕ → Type u22} {K : ℕ → Type u23} [∀ j, Fintype (V j)] [∀ j, Fintype (I j)] [∀ j, DecidableEq (V j)]
  [∀ j, Field (K j)] [∀ j, NumberField (K j)]
variable (G : ∀ j, Core.Fibers (V j) (I j)) (θ γ c : ℝ) (η : ℕ → ℝ)
  (Z₁ Z₂ : ∀ j, V j → K j) (h₁ : ∀ j, Function.Injective (Z₁ j)) (h₂ : ∀ j, Function.Injective (Z₂ j))

theorem arithmetic_no_unbounded (hθ : 0<θ) (hγ : 0<γ) (hγ1 : γ<1) (hc : 0<c) (hcγ : c<γ)
    (hn : Tendsto (fun j => (Fintype.card (V j):ℝ)) atTop atTop)
    (hη : Tendsto η atTop (𝓝 0)) (hη0 : ∀ j, 0≤η j) (hηb : ∀ j, η j≤θ/2)
    (hG : ∀ j, PreparedGraph (V j) (I j) (G j) θ γ c (η j))
    (t : ∀ j, I j → K j) (ht : ∀ j e y, y∈(G j).targets e →
      (Z₁ j ((G j).source e)-Z₁ j y)*(Z₂ j ((G j).source e)-Z₂ j y)=t j e)
    (hWtop : Tendsto (fun j => overlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)) atTop atTop) : False := by
  sorry
end WeakPinned

end
end
end
end

end OAI
end
