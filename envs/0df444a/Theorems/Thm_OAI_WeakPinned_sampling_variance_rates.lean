-- Prove2me | Theorems.Thm_OAI_WeakPinned_sampling_variance_rates
-- name    : OAI.WeakPinned.sampling_variance_rates
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T01:02:58.312557+00:00
-- url     : https://prove2.me/theorems/b7682e2f-c11b-4d11-b445-2d63051c07ec
-- title:
--   On prepared fiber graphs with arithmetic fibers, the fiber and incoming sampling variances are small against the overlap and potential scales (OpenAI weak pinned distances)
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
--   **The quantities.** For a cell $C \subseteq V_j$, $m_j(C)$ (`totalMass`) is the sum of the arithmetic cell masses `cellMass` of $C$ for $Z^1_j$ and for $Z^2_j$. The cell mass of $C$ adds up, over the places of $K_j$, the scale-integrated multiplicity with which $C$ occurs as a cluster in the hierarchy of the points $Z(x)$ at that place. Archimedean places are averaged over random grids and weighted by `archWeight`; the finitely many bad finite places are weighted by $1/[K_j : \mathbb Q]$.
--
--   - The overlap scale is $W_j = \sum_C m_j(C)\, \frac{|C|(|C|-1)}{N_j(N_j-1)}$ (`overlapScale`).
--   - The potential scale $A_j$ (`potentialScale`) is the average over $x \in V_j$ of the arithmetic potentials `Global.S` of $x$ for $Z^1_j$ and $Z^2_j$.
--   - For a family of weights $w_i$ and sets $B_i$, a threshold $T$ and a cell $D$, write $p_B(D) = |B \cap D|/|B|$ and $p(D) = |D|/N_j$. The cell variance `varianceCell` is $\sum_i w_i (p_{B_i}(D) - p(D))^2$ if $T < |D|$. Otherwise it is $\tfrac12 \sum_i w_i\, p_{B_i}(D)^2$, summed over the $i$ with $p_{B_i}(D) \ge 2/|B_i|$.
--   - The fiber variance $\Phi_j$ (`fiberVariance`) is $\sum_C m_j(C)$ times the cell variance of the fiber family (weights $|B_e|/\#\text{edges}$, sets $B_e$) at threshold $N_j^{1-c}$.
--   - The incoming variance $\Psi_j$ (`incomingVariance`) is the same with the incoming family. A vertex $y$ with at least $N_j^\gamma$ incoming edges gets the weight $\#\text{incoming}(y)/\#\text{edges}$ and the set of its in-neighbours; every other vertex gets weight $0$ and the set $V_j$.
--
--   **The statement.** Under these assumptions,
--   $$\frac{\Phi_j}{W_j + A_j + 1} \to 0 \qquad\text{and}\qquad \frac{\Psi_j}{W_j + A_j + 1} \to 0 \qquad (j \to \infty).$$
--   No bound on the degrees of the number fields $K_j$ is assumed.
--
--   Lean: `OAI.WeakPinned.sampling_variance_rates`, OpenAI's lemma of that name (in `lean/OAI/Geometry/PinnedDistances/OverlapRates.lean`). `Core.Fibers`, `PreparedGraph`, `overlapScale`, `potentialScale`, `totalMass`, `fiberVariance` and `incomingVariance` come from the definitions bundle `OAIQWWP000` of this split.
-- source:
--   OpenAI, The weak pinned planar distance theorem, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 167; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-weak-pinned-planar-distance-theorem-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/PinnedDistances/OverlapRates.lean (declaration OAI.WeakPinned.sampling_variance_rates)

import Mathlib
import Definitions.Def_OAIQWWP000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter
open scoped Topology

namespace WeakPinned
open Filter Variance Global
open scoped Topology BigOperators
variable {V : ℕ → Type u6} {I : ℕ → Type u7} {K : ℕ → Type u8} [∀ j, Fintype (V j)] [∀ j, Fintype (I j)] [∀ j, DecidableEq (V j)]
  [∀ j, Field (K j)] [∀ j, NumberField (K j)]
variable (G : ∀ j, Core.Fibers (V j) (I j)) (θ γ c : ℝ) (η : ℕ → ℝ)
  (Z₁ Z₂ : ∀ j, V j → K j) (h₁ : ∀ j, Function.Injective (Z₁ j)) (h₂ : ∀ j, Function.Injective (Z₂ j))

theorem sampling_variance_rates (hθ : 0<θ) (hγ : 0<γ) (hγ1 : γ<1) (hcγ : c<γ)
    (hn : Tendsto (fun j => (Fintype.card (V j):ℝ)) atTop atTop)
    (hη : Tendsto η atTop (𝓝 0)) (hη0 : ∀ j, 0≤η j) (hηb : ∀ j, η j≤θ/2)
    (hG : ∀ j, PreparedGraph (V j) (I j) (G j) θ γ c (η j))
    (t : ∀ j, I j → K j) (ht : ∀ j e y, y ∈ (G j).targets e →
      (Z₁ j ((G j).source e)-Z₁ j y)*(Z₂ j ((G j).source e)-Z₂ j y)=t j e) :
    Tendsto (fun j => fiberVariance G c Z₁ Z₂ h₁ h₂ j /
      (overlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+potentialScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+1)) atTop (𝓝 0) ∧
    Tendsto (fun j => incomingVariance G γ c Z₁ Z₂ h₁ h₂ j /
      (overlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+potentialScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+1)) atTop (𝓝 0) := by
  sorry

end WeakPinned

end
end
end
end
end
end
end
end
end

end OAI
end
