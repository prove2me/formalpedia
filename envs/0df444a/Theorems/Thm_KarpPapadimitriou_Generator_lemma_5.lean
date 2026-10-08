-- Prove2me | Theorems.Thm_KarpPapadimitriou_Generator_lemma_5
-- name    : KarpPapadimitriou.Generator.lemma_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:41:10.471998+00:00
-- url     : https://prove2.me/theorems/046b9c84-1637-448c-b9f8-f001e7dce584
-- title:
--   Lemma 5 — projection distance for independent small hyperplanes
-- statement:
--   Let $H_0,\ldots,H_{j+1}$ be affinely independent small hyperplanes, let $r$ lie on $H_0,\ldots,H_j$, and put $\delta=\operatorname{dist}(r,H_{j+1})$. For the paper's parameter $t$,
--   $$\operatorname{dist}\Bigl(r,\bigcap_{i=0}^{j+1}H_i\Bigr)\le(2^t-1)\delta.$$
--
--   This bounds the movement caused by adding one independent equality to the current flat.
--
--   **Formalization Note** All distances use the Euclidean metric on real space. The report's proof shifts between indices $0,\ldots,j+1$ and $1,\ldots,j$; the theorem follows its stated indices.
-- source:
--   Karp & Papadimitriou, On linear characterizations of combinatorial optimization problems, MIT/LCS/TM-154 (Feb. 1980), p. 13, Lemma 5

import Mathlib
import Definitions.Def_KarpPapadimitriou_Generator_Hyperplanes

namespace KarpPapadimitriou.Generator

/-- Lemma 5: projecting onto one additional independent small hyperplane increases the
distance by at most the displayed factor. -/
theorem lemma_5 (n P j : ℕ) (c : Fin n → ℤ) (k : ℤ)
    (H : Fin (j + 2) → (Fin n → ℤ) × ℤ)
    (r : EuclideanSpace ℝ (Fin n))
    (hsmall : ∀ i, SmallHyperplane P (H i).1 (H i).2)
    (hind : IndependentNormals H)
    (hr : ∀ i : Fin (j + 2), i.val ≤ j → r ∈ hyperplane (H i).1 (H i).2) :
    Metric.infDist r (flat H) ≤
      ((2 : ℝ) ^ tParam n P c k - 1) *
        hyperplaneDistance (H ⟨j + 1, by omega⟩).1 (H ⟨j + 1, by omega⟩).2 r := by sorry

end KarpPapadimitriou.Generator
