-- Prove2me | Theorems.Thm_OnlineColoringKYY_lemma_4_3
-- name    : OnlineColoringKYY.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:30:17.999201+00:00
-- url     : https://prove2.me/theorems/23e9a87b-ce7c-40d8-b7a2-0f3cd10eb58a
-- title:
--   Lemma 4.3 — a $2\ell$-colorable graph on $2^\ell$ vertices with every color used at most twice
-- statement:
--   Let $\ell \ge 1$ be an integer. For every proper deterministic online coloring algorithm $A$ there is a graph $G$ on $2^\ell$ vertices, presented in some order, such that $G$ is $2\ell$-colorable and $A$ uses each of its colors on at most two vertices of $G$:
--   $$
--   \chi(G) \le 2\ell, \qquad \bigl|\{v : c_A^G(v) = c_0\}\bigr| \le 2 \ \text{ for every color } c_0 .
--   $$
--
--   In the paper's words, the adversary has a strategy that forces the player to use each color in at most two vertices on a $2\ell$-colorable graph with $2^\ell$ vertices. In particular $A$ uses at least $2^{\ell-1}$ colors on a graph of chromatic number at most $2\ell$.
--
--   Differences from the source:
--   - encoding: the adversary has a strategy that forces the player → for every proper algorithm A there exists a graph G on which A; reason: against a deterministic player an adaptive adversary strategy yields exactly one graph built in response to it
--   - reading: a 2ℓ-colorable graph with 2ℓvertices (superscript flattened in the text layer) → G : SimpleGraph (Fin (2 ^ ℓ)), G.Colorable (2 * ℓ); reason: the rendered page prints 2^ℓ vertices; the proof of Theorem 1.1 says 'note that n ≤ 2^ℓ'
--   - encoding: vertices of the input arrive one by one → G : SimpleGraph (Fin n) with vertex i the (i+1)-st arrival; reason: any arrival order is a bijection with Fin n; same instances
--   - encoding: a deterministic online algorithm colors each arriving vertex immediately, seeing the graph so far → OnlineColoringAlg: the color of the newest vertex as a function of the prefix graph on Fin (m+1); properness on every input (IsProper); reason: the earlier colors of a deterministic algorithm are functions of the earlier prefixes, so this is exactly the class of deterministic online algorithms
-- source:
--   Kawarabayashi–Yoneda–Yoneda, Online Graph Coloring: Competitive Ratios Separating Randomized and Deterministic Algorithms, STOC 2027 submission (manuscript sha256 3d1eeea6…), Lemma 4.3, printed p.13 (PDF p.15)

import Mathlib
import Definitions.Def_OnlineColoringKYY_OnlineColoringAlg
import Definitions.Def_OnlineColoringKYY_prefixGraph
import Definitions.Def_OnlineColoringKYY_run
import Definitions.Def_OnlineColoringKYY_IsProper

set_option autoImplicit false

namespace OnlineColoringKYY

/-- **Lemma 4.3** (Kawarabayashi–Yoneda–Yoneda, *Online Graph Coloring: Competitive Ratios Separating Randomized and Deterministic Algorithms*, STOC 2027 submission (manuscript sha256 3d1eeea6…), Lemma 4.3, printed p.13 = PDF p.15). Let `ℓ ≥ 1` be an integer. The
adversary has a strategy that forces the player to use each color in at most two vertices on a
`2ℓ`-colorable graph with `2^ℓ` vertices.

In Lean: for every proper deterministic online coloring algorithm `A` there is a `2ℓ`-colorable
graph `G` on `2^ℓ` vertices (arriving in the order `0, 1, …, 2^ℓ − 1`) on which every color of `A`
is used on at most two vertices.

**Formalization Note** Against a deterministic player, an adaptive adversary strategy produces
one graph, built in response to that player; the existence of that graph for every algorithm is
exactly what the strategy gives, and conversely the graph is all the lemma's conclusion speaks
about. The printed "`2ℓ` vertices" is `2^ℓ` (superscript in the rendered page; "note that
`n ≤ 2^ℓ`" in the proof of Theorem 1.1). -/
theorem lemma_4_3 (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (A : OnlineColoringAlg) (hA : IsProper A) :
    ∃ G : SimpleGraph (Fin (2 ^ ℓ)), G.Colorable (2 * ℓ) ∧
      ∀ c : ℕ, (Finset.univ.filter (fun v => run A G v = c)).card ≤ 2 := by sorry

end OnlineColoringKYY
