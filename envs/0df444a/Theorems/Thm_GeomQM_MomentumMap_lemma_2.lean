-- Prove2me | Theorems.Thm_GeomQM_MomentumMap_lemma_2
-- name    : GeomQM.MomentumMap.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:25:34.76302+00:00
-- url     : https://prove2.me/theorems/bc9813c0-4f40-4108-ac2d-3b27c8fa0968
-- title:
--   Lemma 2, p. 5 — the Hermitian matrices with A ◦ B = ½(AB + BA) form a Jordan algebra
-- statement:
--   Let $x,y$ be Hermitian $n\times n$ complex matrices and $x\circ y=\tfrac12(xy+yx)$ the Jordan product (6). Then $x\circ y$ is Hermitian, the product is commutative, $x\circ y=y\circ x$, and it satisfies the Jordan identity of Definition 1: writing $x^2=x\circ x$,
--
--   $$(x\circ y)\circ x^2=x\circ(y\circ x^2).$$
--
--   So $(\mathcal O,\circ)$ is a Jordan algebra. Its symmetric tensor is the Jordan tensor $\mathcal R$ that Proposition 5 pulls back to the Euclidean structure of Hilbert space.
--
--   **Formalization Note** In the identity $(xy)x^2=x(yx^2)$ of Definition 1, every product, including the square, is the Jordan product.
-- source:
--   Cariñena, Clemente-Gallardo & Marmo, Geometrization of Quantum Mechanics, arXiv:math-ph/0701053v2, p. 5, Definition 1 and Lemma 2, eq. (6)

import Mathlib
import Definitions.Def_GeomQM_MomentumMap_Defs

namespace GeomQM.MomentumMap
open Matrix
theorem lemma_2 (n : ℕ) (x y : Matrix (Fin n) (Fin n) ℂ)
    (hx : x.IsHermitian) (hy : y.IsHermitian) :
    (jordan x y).IsHermitian ∧
    jordan x y = jordan y x ∧
    jordan (jordan x y) (jordan x x) = jordan x (jordan y (jordan x x)) := by sorry
end GeomQM.MomentumMap
