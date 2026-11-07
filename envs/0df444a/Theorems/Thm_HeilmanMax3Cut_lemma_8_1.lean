-- Prove2me | Theorems.Thm_HeilmanMax3Cut_lemma_8_1
-- name    : HeilmanMax3Cut.lemma_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:30:29.397197+00:00
-- url     : https://prove2.me/theorems/5605eaf7-b211-4a6b-9a3e-fb13bef8006d
-- title:
--   Lemma 8.1 — joint signed arc bound
-- statement:
--   Let $K_a(p,q)$ be the opposing-arc overlap (58), $b=1/3$, and $\tau(a)=4P(a)-3k(a)$, $j(a)=P(a)-3k(a)$ with $k(a)=K_a(b,b)$, $P(a)=\partial_1K_a(b,b)$ (65). Let $\Delta_3=\{z\in[0,1]^3:\sum_iz_i=1\}$.
--
--   1. For every $a\ge0$ and $p,q\in\Delta_3$, with $x=p-b\mathbf 1$ and $y=q-b\mathbf 1$,
--   $$\sum_{i=1}^3K_a(p_i,q_i)-3K_a(b,b)\ \ge\ \tau(a)\langle x,y\rangle+j(a)\bigl(\|x\|^2+\|y\|^2\bigr).$$
--   2. $j(a)>0$ for every $a>0$.
--
--   The lemma lower-bounds the conditional noise stability of three pairs of opposing arcs by a quadratic form in the deviations of the arc lengths from $1/3$; it is the angular half of the proof of Theorem 7.1.
--
--   Differences from the source:
--   - encoding: x = p − b1, y = q − b1 in ℝ³ with ⟨x, y⟩ and ‖x‖² → functions Fin 3 → ℝ with ∑ᵢ (pᵢ − 1/3)(qᵢ − 1/3) and ∑ᵢ (pᵢ − 1/3)²; reason: the same Euclidean quantities written in coordinates
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Lemma 8.1, Eq. (67), p.24

import Mathlib
import Definitions.Def_HeilmanMax3Cut_Delta3
import Definitions.Def_HeilmanMax3Cut_Karc
import Definitions.Def_HeilmanMax3Cut_tauA
import Definitions.Def_HeilmanMax3Cut_jA

namespace HeilmanMax3Cut

/-- **Lemma 8.1 (joint signed arc bound).** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Lemma 8.1, Eq. (67), p.24: "For every `a ≥ 0` and
`p, q ∈ Δ₃`, with `b = 1/3` as above, put `x = p − b1` and `y = q − b1`. Then
`∑_{i=1}^3 K_a(pᵢ, qᵢ) − 3K_a(b, b) ≥ τ(a)⟨x, y⟩ + j(a)(‖x‖² + ‖y‖²)`. Moreover, `j(a) > 0` when
`a > 0`."

**Formalization Note.** `⟨x, y⟩ = ∑ᵢ xᵢyᵢ` and `‖x‖² = ∑ᵢ xᵢ²` on `ℝ³ = Fin 3 → ℝ`; `K_a` is (58),
`τ, j` are (65). Both clauses are stated. -/
theorem lemma_8_1 :
    (∀ a : ℝ, 0 ≤ a → ∀ p ∈ Delta3, ∀ q ∈ Delta3,
      tauA a * (∑ i, (p i - 1 / 3) * (q i - 1 / 3)) +
          jA a * (∑ i, (p i - 1 / 3) ^ 2 + ∑ i, (q i - 1 / 3) ^ 2) ≤
        ∑ i, Karc a (p i) (q i) - 3 * Karc a (1 / 3) (1 / 3)) ∧
    ∀ a : ℝ, 0 < a → 0 < jA a := by sorry

end HeilmanMax3Cut
