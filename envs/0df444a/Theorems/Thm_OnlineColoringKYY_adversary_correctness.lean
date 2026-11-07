-- Prove2me | Theorems.Thm_OnlineColoringKYY_adversary_correctness
-- name    : OnlineColoringKYY.adversary_correctness
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:33:03.220012+00:00
-- url     : https://prove2.me/theorems/c697704b-5e6d-40d3-93d6-811c45e0a9b3
-- title:
--   Section 4.2, "Correctness" — the adversary's graph is $2\ell$-colorable by the deferred base coloring
-- statement:
--   Let $\ell \ge 1$ and $n \ge 0$, let $x_0, \dots, x_{n-1} \in \{0,1\}^\ell$ be pairwise distinct codes, let $A$ be a proper deterministic online coloring algorithm, and let $G = G_{A,x,n}$ be the graph built against $A$ by the adversary of Section 4.2, with online colors $c$. Then
--
--   1. $G$ is $2\ell$-colorable;
--   2. for every assignment $\psi$ of base colors such that $\psi(v) = \varphi(v)$ is the base color fixed at pairing for every paired vertex $v$ (some $w \ne v$ has $c(w) = c(v)$), and $\psi(v)$ is an arbitrary element of $X_v$ for every unpaired vertex $v$, the map $\psi$ is a proper coloring of $G$ with values in $\{0, \dots, 2\ell - 1\}$:
--   $$
--   uv \in E(G) \implies \psi(u) \ne \psi(v), \qquad \psi(v) < 2\ell \ \text{ for all } v .
--   $$
--
--   Together with the previous milestone this proves Lemma 4.3.
--
--   Differences from the source:
--   - reading: assign φ(v) to an arbitrary element of X_v (unpaired v) → every ψ with ψ v ∈ X_v on unpaired v and ψ v = baseColor v w on paired v is proper with values < 2ℓ; reason: the strongest reading of 'arbitrary': every such choice works
--   - encoding: admissible sets X_v ⊆ {1,…,2ℓ} with exactly one of {2s−1,2s} for each s, distinct for distinct v → X_v = {2s + code v s : s < ℓ} for code : ℕ → Fin ℓ → Bool injective on the arrivals; reason: bijection between such sets and codes; distinct sets = injective code
--   - encoding: base colors 2s−1, 2s for s ∈ {1,…,ℓ} → base colors 2s, 2s+1 for s ∈ Fin ℓ (0-indexed); reason: shift by one; same instances
--   - encoding: choose s such that 2s−1 is in exactly one of X_v1, X_v2 (any such s) → baseColor uses the least coordinate where the codes differ; reason: fixes one admissible choice of the adversary's strategy; the paper's argument works for every choice
--   - encoding: vertices of the input arrive one by one → G : SimpleGraph (Fin n) with vertex i the (i+1)-st arrival; reason: any arrival order is a bijection with Fin n; same instances
--   - encoding: a deterministic online algorithm colors each arriving vertex immediately, seeing the graph so far → OnlineColoringAlg: the color of the newest vertex as a function of the prefix graph on Fin (m+1); properness on every input (IsProper); reason: the earlier colors of a deterministic algorithm are functions of the earlier prefixes, so this is exactly the class of deterministic online algorithms
-- source:
--   Kawarabayashi–Yoneda–Yoneda, Online Graph Coloring: Competitive Ratios Separating Randomized and Deterministic Algorithms, STOC 2027 submission (manuscript sha256 3d1eeea6…), Section 4.2, "Correctness", printed p.14 (PDF p.16)

import Mathlib
import Definitions.Def_OnlineColoringKYY_OnlineColoringAlg
import Definitions.Def_OnlineColoringKYY_prefixGraph
import Definitions.Def_OnlineColoringKYY_run
import Definitions.Def_OnlineColoringKYY_IsProper
import Definitions.Def_OnlineColoringKYY_admits
import Definitions.Def_OnlineColoringKYY_baseColor
import Definitions.Def_OnlineColoringKYY_advEdge
import Definitions.Def_OnlineColoringKYY_stepGraph
import Definitions.Def_OnlineColoringKYY_advColors
import Definitions.Def_OnlineColoringKYY_advGraph

set_option autoImplicit false

namespace OnlineColoringKYY

/-- **Correctness of the deferred base coloring** (Kawarabayashi–Yoneda–Yoneda, *Online Graph Coloring: Competitive Ratios Separating Randomized and Deterministic Algorithms*, STOC 2027 submission (manuscript sha256 3d1eeea6…), Section 4.2, "Correctness", printed p.14
= PDF p.16).

Let `ℓ ≥ 1`, let `A` be a proper deterministic online coloring algorithm, let `code` give pairwise
distinct admissible sets `X_v` to the arrivals `0, …, n − 1`, and let `G = advGraph A code n`.
Then `G` is `2ℓ`-colorable. Moreover, let `ψ` be any base coloring that gives every paired vertex
`v` (one sharing its online color with some `w ≠ v`) the base color `baseColor code v w` assigned
by the adversary, and every unpaired vertex an arbitrary element of `X_v`. Then `ψ` is a proper
coloring of `G` with values in `{0, …, 2ℓ − 1}`.

**Formalization Note** Base colors are 0-indexed (`2s, 2s + 1` for the paper's `2s − 1, 2s`).
Both conclusions of the paragraph are kept, and "an arbitrary element of `X_v`" is read in its
strongest form: every such choice gives a proper coloring. -/
theorem adversary_correctness (ℓ n : ℕ) (hℓ : 1 ≤ ℓ) (code : ℕ → Fin ℓ → Bool)
    (hcode : Set.InjOn code (Set.Iio n)) (A : OnlineColoringAlg) (hA : IsProper A) :
    (advGraph A code n).Colorable (2 * ℓ) ∧
      ∀ ψ : Fin n → ℕ,
        (∀ v w : Fin n, v ≠ w → run A (advGraph A code n) v = run A (advGraph A code n) w →
            ψ v = baseColor code v.val w.val) →
        (∀ v : Fin n, (∀ w : Fin n, w ≠ v →
            run A (advGraph A code n) w ≠ run A (advGraph A code n) v) →
            admits code v.val (ψ v)) →
        (∀ u v : Fin n, (advGraph A code n).Adj u v → ψ u ≠ ψ v) ∧ ∀ v, ψ v < 2 * ℓ := by sorry

end OnlineColoringKYY
