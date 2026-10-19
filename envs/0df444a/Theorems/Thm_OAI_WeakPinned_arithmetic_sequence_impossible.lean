-- Prove2me | Theorems.Thm_OAI_WeakPinned_arithmetic_sequence_impossible
-- name    : OAI.WeakPinned.arithmetic_sequence_impossible
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T01:02:55.288684+00:00
-- url     : https://prove2.me/theorems/aad19e2f-b47b-4979-93a1-2fe80635f415
-- title:
--   No sequence of growing prepared fiber graphs has fibers that are level sets of a product of two number-field coordinates (OpenAI weak pinned distances)
-- statement:
--   **The setting.** For each $j \in \mathbb N$ let $V_j$ and $I_j$ be finite types, $N_j = |V_j|$, and let $K_j$ be a number field. Let $G_j$ be a fiber graph on $V_j$ (`Core.Fibers`). Each index $e \in I_j$ has a source $\sigma(e) \in V_j$ and a set of targets $B_e \subseteq V_j$ not containing $\sigma(e)$, and indices with the same source have disjoint target sets. The edges of $G_j$ are the pairs $(\sigma(e), y)$ with $y \in B_e$. Let $Z^1_j, Z^2_j : V_j \to K_j$ be injective. Let $\theta > 0$, $0 < \gamma < 1$ and $0 < c < \gamma$ be reals, and let $\eta_j$ be reals with $0 \le \eta_j \le \theta/2$ and $\eta_j \to 0$.
--
--   **The statement.** The following assumptions are contradictory:
--
--   - $N_j \to \infty$;
--   - each $G_j$ is a `PreparedGraph` with parameters $\theta, \gamma, c, \eta_j$. With $N = N_j$ and $\lambda = 1/\log N$, this means:
--     - $N \ge 2$;
--     - the number of edges lies between $(\theta - \eta_j) N(N-1)$ and $(\theta + \eta_j/8) N(N-1)$;
--     - every vertex meets at least $2(\theta - \eta_j)(N-1)$ edges;
--     - every target set has more than $N^\gamma$ elements;
--     - for every vertex set $D$, the heavy count (the sum of $|B_e \cap D|$ over the indices $e$ with $\sigma(e) \in D$ and $|B_e \cap D| \ge \lambda |B_e|$) is at most $(\theta + \eta_j)|D|(|D|-1)$, and at most $\eta_j |D|(|D|-1)$ when $|D| \le N^{1-c}$;
--   - the fibers are arithmetic: there are $t_j(e) \in K_j$ with
--   $$\bigl(Z^1_j\sigma(e) - Z^1_j y\bigr)\bigl(Z^2_j\sigma(e) - Z^2_j y\bigr) = t_j(e) \qquad \text{for all } e \in I_j \text{ and } y \in B_e.$$
--
--   The number fields $K_j$ may vary with $j$, with no bound on their degrees. In OpenAI's proof of the weak pinned distance theorem, a planar counterexample gives such a sequence: its rich distance fibers become level sets of $(Z^1 x - Z^1 y)(Z^2 x - Z^2 y)$ after the planar configuration is moved into a number field containing $\sqrt{-1}$.
--
--   Lean: `OAI.WeakPinned.arithmetic_sequence_impossible`, OpenAI's theorem of that name (in `lean/OAI/Geometry/PinnedDistances/ArithmeticContradiction.lean`), with conclusion `False`. `Core.Fibers` and `PreparedGraph` come from the definitions bundle `OAIQWWP000` of this split.
-- source:
--   OpenAI, The weak pinned planar distance theorem, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 167; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-weak-pinned-planar-distance-theorem-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/PinnedDistances/ArithmeticContradiction.lean (declaration OAI.WeakPinned.arithmetic_sequence_impossible)

import Mathlib
import Definitions.Def_OAIQWWP000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

section
noncomputable section
open Filter
open scoped Topology
namespace WeakPinned
open Global

variable {V : ℕ → Type u1} {I : ℕ → Type u2} {K : ℕ → Type u3} [∀ j,Fintype (V j)] [∀ j,Fintype (I j)] [∀ j,DecidableEq (V j)]
  [∀ j,Field (K j)] [∀ j,NumberField (K j)]

theorem arithmetic_sequence_impossible
    (G : ∀ j,Core.Fibers (V j) (I j)) (θ γ c : ℝ) (η : ℕ → ℝ)
    (Z₁ Z₂ : ∀ j,V j → K j) (h₁ : ∀ j,Function.Injective (Z₁ j)) (h₂ : ∀ j,Function.Injective (Z₂ j))
    (hθ : 0<θ) (hγ : 0<γ) (hγ1 : γ<1) (hc : 0<c) (hcγ : c<γ)
    (hn : Tendsto (fun j => (Fintype.card (V j):ℝ)) atTop atTop)
    (hη : Tendsto η atTop (𝓝 0)) (hη0 : ∀ j,0≤η j) (hηb : ∀ j,η j≤θ/2)
    (hG : ∀ j,PreparedGraph (V j) (I j) (G j) θ γ c (η j))
    (t : ∀ j,I j → K j) (ht : ∀ j e y,y∈(G j).targets e →
      (Z₁ j ((G j).source e)-Z₁ j y)*(Z₂ j ((G j).source e)-Z₂ j y)=t j e) : False := by
  sorry

end WeakPinned

end
end

end OAI
end
