-- Prove2me | Theorems.Thm_KarpPapadimitriou_Generator_corollary_lemma_4
-- name    : KarpPapadimitriou.Generator.corollary_lemma_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:41:08.610444+00:00
-- url     : https://prove2.me/theorems/25a343a3-9010-49e7-bd52-c40c8f7d36ca
-- title:
--   Corollary after Lemma 4 — separation of disjoint small hyperplanes
-- statement:
--   Let $r$ be any real point in the common flat of an affinely independent family $H_1,\ldots,H_m$ of small hyperplanes. If another small hyperplane $H$ is disjoint from that flat, then, for the same parameter $t$,
--   $$\operatorname{dist}(r,H)\ge 2^{-(n+1)t}.$$
--
--   The bound applies to a real point on the flat, without assuming that its coordinates are rational.
--
--   **Formalization Note** “Affinely independent” means the normals are linearly independent; the intersection is over exactly the listed family, including the empty family when $m=0$.
-- source:
--   Karp & Papadimitriou, On linear characterizations of combinatorial optimization problems, MIT/LCS/TM-154 (Feb. 1980), p. 12, Corollary after Lemma 4

import Mathlib
import Definitions.Def_KarpPapadimitriou_Generator_Hyperplanes

namespace KarpPapadimitriou.Generator

/-- Corollary after Lemma 4: the distance gap is constant on a flat disjoint from the new
hyperplane, including when the point on the flat is not rational. -/
theorem corollary_lemma_4 (n P m : ℕ) (c : Fin n → ℤ) (k : ℤ)
    (H : Fin m → (Fin n → ℤ) × ℤ) (f : Fin n → ℤ) (g : ℤ)
    (r : EuclideanSpace ℝ (Fin n))
    (hsmall : ∀ i, SmallHyperplane P (H i).1 (H i).2)
    (hsmall_new : SmallHyperplane P f g)
    (hind : IndependentNormals H)
    (hr : r ∈ flat H)
    (hdisjoint : hyperplane f g ∩ flat H = ∅) :
    (1 : ℝ) / 2 ^ ((n + 1) * tParam n P c k) ≤ hyperplaneDistance f g r := by sorry

end KarpPapadimitriou.Generator
