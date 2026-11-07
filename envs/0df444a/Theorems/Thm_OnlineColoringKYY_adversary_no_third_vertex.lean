-- Prove2me | Theorems.Thm_OnlineColoringKYY_adversary_no_third_vertex
-- name    : OnlineColoringKYY.adversary_no_third_vertex
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:32:40.630633+00:00
-- url     : https://prove2.me/theorems/aa55bd51-2991-4fa7-928f-a76572a22970
-- title:
--   Section 4.2 — the adversary never lets a color be used on a third vertex
-- statement:
--   Let $\ell, n \ge 0$, let $x_0, \dots, x_{n-1} \in \{0,1\}^\ell$ be pairwise distinct codes (distinct admissible sets $X_v$), and let $A$ be a proper deterministic online coloring algorithm. Let $G = G_{A,x,n}$ be the graph built against $A$ by the adversary of Section 4.2 and $c$ the colors $A$ assigns to it online. Then for every color $c_0$,
--   $$
--   \bigl|\{v : c(v) = c_0\}\bigr| \le 2 .
--   $$
--
--   This is the first half of the proof of Lemma 4.3: each time a paired color class $\{u_1, u_2\}$ exists, one of its two base colors is outside $X_v$, so that vertex is joined to the newcomer $v$ and properness forbids the color for $v$.
--
--   Differences from the source:
--   - reading: it is impossible for the player to select an online color that has already been used on two vertices → every color class of A on advGraph has at most two vertices; reason: the impossibility at every arrival is the same as every color class having size at most two
--   - encoding: admissible sets X_v ⊆ {1,…,2ℓ} with exactly one of {2s−1,2s} for each s, distinct for distinct v → X_v = {2s + code v s : s < ℓ} for code : ℕ → Fin ℓ → Bool injective on the arrivals; reason: bijection between such sets and codes; distinct sets = injective code
--   - encoding: base colors 2s−1, 2s for s ∈ {1,…,ℓ} → base colors 2s, 2s+1 for s ∈ Fin ℓ (0-indexed); reason: shift by one; same instances
--   - encoding: choose s such that 2s−1 is in exactly one of X_v1, X_v2 (any such s) → baseColor uses the least coordinate where the codes differ; reason: fixes one admissible choice of the adversary's strategy; the paper's argument works for every choice
--   - encoding: vertices of the input arrive one by one → G : SimpleGraph (Fin n) with vertex i the (i+1)-st arrival; reason: any arrival order is a bijection with Fin n; same instances
--   - encoding: a deterministic online algorithm colors each arriving vertex immediately, seeing the graph so far → OnlineColoringAlg: the color of the newest vertex as a function of the prefix graph on Fin (m+1); properness on every input (IsProper); reason: the earlier colors of a deterministic algorithm are functions of the earlier prefixes, so this is exactly the class of deterministic online algorithms
-- source:
--   Kawarabayashi–Yoneda–Yoneda, Online Graph Coloring: Competitive Ratios Separating Randomized and Deterministic Algorithms, STOC 2027 submission (manuscript sha256 3d1eeea6…), Section 4.2, "Adversary algorithm", printed p.13 (PDF p.15)

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

/-- **No third vertex** (Kawarabayashi–Yoneda–Yoneda, *Online Graph Coloring: Competitive Ratios Separating Randomized and Deterministic Algorithms*, STOC 2027 submission (manuscript sha256 3d1eeea6…), Section 4.2, "Adversary algorithm", printed p.13 = PDF p.15:
"With this method, it is impossible for the player to select an online color that has already been
used on two vertices").

Let `A` be a proper deterministic online coloring algorithm and let `code` give pairwise distinct
admissible sets `X_v` to the arrivals `0, …, n − 1`. On the graph `advGraph A code n` built by the
adversary of Section 4.2, every color of `A` is used on at most two vertices.

**Formalization Note** "Impossible to select a color already used on two vertices", applied at
every arrival, is "every color class has at most two vertices". Any injective code is allowed (the
paper uses some choice of distinct `X_v`). -/
theorem adversary_no_third_vertex (ℓ n : ℕ) (code : ℕ → Fin ℓ → Bool)
    (hcode : Set.InjOn code (Set.Iio n)) (A : OnlineColoringAlg) (hA : IsProper A) (c : ℕ) :
    (Finset.univ.filter (fun v : Fin n => run A (advGraph A code n) v = c)).card ≤ 2 := by sorry

end OnlineColoringKYY
