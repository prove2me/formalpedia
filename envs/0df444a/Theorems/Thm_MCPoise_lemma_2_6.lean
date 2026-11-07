-- Prove2me | Theorems.Thm_MCPoise_lemma_2_6
-- name    : MCPoise.lemma_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:37:11.636043+00:00
-- url     : https://prove2.me/theorems/e218879b-191a-47b3-9920-57e074c17cb8
-- title:
--   Lemma 2.6 — group flow load at most $\min\{1, 2\rho^3 \sum_{r_{j,\ell} \in V(C)} x_{e,j}\}$
-- statement:
--   Let $(x, f, \lambda)$ be feasible for Junction-LP, let $\rho \ge 128 \log_2(2k)$ be an integer, and let $\mathcal C$ be returned by a run of Algorithm 1. For $e \in E$ and $C \in \mathcal C$ put
--   $$x_{e,C} := \min\Big\{1,\ 2\rho^3 \sum_{r_{j,\ell} \in V(C)} x_{e,j}\Big\}.$$
--
--   **Lemma 2.6.** For each terminal $t \in \bigcup_{z_i \in Z_C}\{s_i, t_i\}$, the unit flow from $t$ to $s^*_C$ given by the algorithm has load at most $x_{e,C}$ on each $e \in E$.
--
--   These capacities give the feasible point of Multiroot-LP used in the proof of Theorem 1.7.
--
--   Differences from the source:
--   - generalization: the unit flow given by the algorithm → every flow of the construction of p.12, with any sub-flows, coupling and cycle deletion, on every run; reason: the page leaves those open and the proof bounds each of them
--   - reading: ρ ≥ 128 log(2k), base not printed → 128 log₂(2k) ≤ ρ; reason: Lemma 2.5's last line needs base 2: 64 log₂ k/(128 ln k) > 1/2
--   - encoding: terminal t ∈ ∪{s_i, t_i} → the label (i, b) of the demand occurrence; reason: footnote 2, p.9: a vertex in several demands has separate flow variables
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Lemma 2.6, p.15

import Mathlib
import Definitions.Def_MCPoise_JunctionLPFeasible
import Definitions.Def_MCPoise_auxGraph
import Definitions.Def_MCPoise_AssignRun
import Definitions.Def_MCPoise_IsGroupFlow

namespace MCPoise

/-- **Lemma 2.6 (load of a group flow).**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Lemma 2.6, p.15: "Let 𝒞 be the collection of groups returned by Algorithm 1. For each edge e ∈ E(G) and group C ∈ 𝒞, set
x_{e,C} := min{1, 2ρ³ Σ_{r_{j,ℓ}∈V(C)} x_{e,j}}. For each terminal t ∈ ∪_{z_i∈Z_C}{s_i, t_i}, the unit flow from t to s*_C given by the algorithm induces load
at most x_{e,C} on each e ∈ E(G)."

**Formalization Note.** The bound holds for every flow of the construction of p.12 (`IsGroupFlow`), the same predicate as Lemma 2.3. The clause `min{1, …}` is
real: `load ≤ 1` holds because the paths are simple, after the cycle deletion of footnote 4. The sum over `V(C)` counts each root copy, so a root with
several copies in `C` counts several times. -/
theorem lemma_2_6 (I : Inst) (L : ℕ) (x : Sym2 (Fin I.n) → ℝ) (x' : Sym2 (Fin I.n) → Fin I.k → ℝ)
    (lam : Fin I.k → Fin I.k → ℝ) (f : Fin I.k → Bool → Fin I.k → List (Fin I.n) → ℝ) (ρ : ℕ)
    (hLP : JunctionLPFeasible I L x x' lam f)
    (hρ : 128 * Real.logb 2 (2 * (I.k : ℝ)) ≤ (ρ : ℝ))
    (𝒞 : Set (AGroup (auxGraph lam))) (hrun : AssignRun ρ (auxInit lam) 𝒞)
    (G : AGroup (auxGraph lam)) (hG : G ∈ 𝒞) (i : Fin I.k) (hi : i ∈ pairsOf G.C) (b : Bool)
    (F : List (List (Fin I.n) × ℝ)) (hF : IsGroupFlow I L f G i b F)
    (e : Sym2 (Fin I.n)) (he : e ∈ I.graph.edgeSet) :
    wLoad F e ≤ min 1 (2 * (ρ : ℝ) ^ 3 * ∑ c ∈ copiesOf G.C, x' e c.1) := by sorry

end MCPoise
