-- Prove2me | Theorems.Thm_OnlineColoringKYY_theorem_1_1_witness_bound
-- name    : OnlineColoringKYY.theorem_1_1_witness_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:30:33.306948+00:00
-- url     : https://prove2.me/theorems/fafcb2eb-774a-4351-99d4-357e77cc1592
-- title:
--   Proof of Theorem 1.1 — an $n$-vertex $2\lceil\log_2 n\rceil$-colorable graph forcing $n/2$ colors
-- statement:
--   Let $n \ge 2$. For every proper deterministic online coloring algorithm $A$ there is a graph $G$ on exactly $n$ vertices such that
--   $$
--   \chi(G) \le 2\lceil \log_2 n \rceil \qquad \text{and} \qquad \mathrm{ALG}_A(G) \ge \frac n2 .
--   $$
--
--   This is the explicit witness of the proof of Theorem 1.1, obtained from Lemma 4.3 with $\ell = \lceil \log_2 n \rceil$ (so that $n \le 2^\ell$). It gives the ratio $\frac{n/2}{2\lceil\log_2 n\rceil}$, which is $\Omega(n/\log n)$. The algorithm may depend on $n$.
--
--   Differences from the source:
--   - encoding: ℓ = ⌈log₂ n⌉; at least n/2 colors → Nat.clog 2 n; n ≤ 2 · numColors A G; reason: Nat.clog 2 n is ⌈log₂ n⌉ for n ≥ 1; the inequality avoids rounding
--   - reading: the bound holds even if the final number of vertices n is known (proof, p.14) → A is quantified after n; reason: an algorithm that knows n is a family n ↦ A_n of algorithms; ∀ n ∀ A covers every such family and is logically the same as ∀ A ∀ n, so no case is added or dropped
--   - encoding: vertices of the input arrive one by one → G : SimpleGraph (Fin n) with vertex i the (i+1)-st arrival; reason: any arrival order is a bijection with Fin n; same instances
--   - encoding: a deterministic online algorithm colors each arriving vertex immediately, seeing the graph so far → OnlineColoringAlg: the color of the newest vertex as a function of the prefix graph on Fin (m+1); properness on every input (IsProper); reason: the earlier colors of a deterministic algorithm are functions of the earlier prefixes, so this is exactly the class of deterministic online algorithms
-- source:
--   Kawarabayashi–Yoneda–Yoneda, Online Graph Coloring: Competitive Ratios Separating Randomized and Deterministic Algorithms, STOC 2027 submission (manuscript sha256 3d1eeea6…), Section 4.3, proof of Theorem 1.1, printed p.14 (PDF p.16)

import Mathlib
import Definitions.Def_OnlineColoringKYY_OnlineColoringAlg
import Definitions.Def_OnlineColoringKYY_prefixGraph
import Definitions.Def_OnlineColoringKYY_run
import Definitions.Def_OnlineColoringKYY_IsProper
import Definitions.Def_OnlineColoringKYY_numColors

set_option autoImplicit false

namespace OnlineColoringKYY

/-- **The witness of Theorem 1.1** (Kawarabayashi–Yoneda–Yoneda, *Online Graph Coloring: Competitive Ratios Separating Randomized and Deterministic Algorithms*, STOC 2027 submission (manuscript sha256 3d1eeea6…), Section 4.3, proof of Theorem 1.1, printed p.14 = PDF
p.16: "for every deterministic algorithm, there exists an input of an `n`-vertex `2ℓ`-colorable
graph such that this algorithm uses at least `n/2` colors", with `ℓ = ⌈log₂ n⌉`).

For every `n ≥ 2` and every proper deterministic online coloring algorithm `A` there is a graph
`G` on exactly `n` vertices that is `2⌈log₂ n⌉`-colorable and on which `A` uses at least `n/2`
colors.

**Formalization Note** `⌈log₂ n⌉` is `Nat.clog 2 n`. "At least `n/2` colors" is
`n ≤ 2 · numColors A G`. The algorithm may depend on `n` (the proof assumes `n` known in
advance): quantifying `A` after `n` covers every such family. -/
theorem theorem_1_1_witness_bound (n : ℕ) (hn : 2 ≤ n) (A : OnlineColoringAlg) (hA : IsProper A) :
    ∃ G : SimpleGraph (Fin n), G.Colorable (2 * Nat.clog 2 n) ∧ n ≤ 2 * numColors A G := by sorry

end OnlineColoringKYY
