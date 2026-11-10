-- Prove2me | Theorems.Thm_HypercliqueCircuits_Circuits_lemma_2
-- name    : HypercliqueCircuits.Circuits.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T00:35:52.660958+00:00
-- url     : https://prove2.me/theorems/b8eeed4c-2957-421b-be15-d825ee1081fc
-- title:
--   Lemma 2 — exact rectangular hyperclique bound
-- statement:
--   Let $k\ge2$, $\ell\ge1$, and $n_i\ge\ell$ for every coordinate. Let $C(\Delta_\ell^{(k)})$ be the actual minimum circuit size. There is an attaining circuit for that minimum and a circuit for the rectangular polynomial satisfying
--
--   $$|C_{(n_1,\ldots,n_k)}|\le C(\Delta_\ell^{(k)})\prod_{i=1}^k\left\lceil\frac{n_i}{\ell}\right\rceil.$$
--
--   The bound is exact: no asymptotic factor or extra summing factor is inserted. The minimum is taken over circuits with the same coefficient ring and size convention. This transfers uniform-dimension circuit bounds to the rectangular contractions used in the source.
--
--   Differences from the source:
--   - generalization: arithmetic circuits in the source coefficient setting → circuits with arbitrary literal coefficients over every commutative ring; reason: the division-free identities apply over these rings and specialize to the dyadic source setting
--   - reading: arithmetic circuit size without a leaf-count convention → total vertices, including all declared variable sources and literal constant sources; output pointers are free; reason: fixes one size convention for every result; sharing and exact factors are audited in MODERATION_NOTES.md
--   - encoding: one-based coordinate tuples and deletion of position j → Fin coordinates and functions on the ordered subtype of positions other than j; reason: the increasing-coordinate bijection preserves all variables and every monomial
--   - encoding: C(T) as smallest circuit size and positive block length → an extended-natural infimum together with an attaining circuit; ceiling (n_i+ell-1)/ell; reason: no empty-set default can trivialize the bound, and positive integer dimensions make this the exact ceiling
-- source:
--   Josh Alman, Baitian Li, Neha Pant, Kevin Pratt, Ryan Williams, Finding Hypercliques Faster Than Brute Force, STOC 2027 submission #1224 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1224.pdf, Lemma 2, p.16 (PDF 17).

import Definitions.Def_HypercliqueCircuits_Circuits_Transpose
import Definitions.Def_HypercliqueCircuits_Circuits_Machine

set_option autoImplicit false

namespace HypercliqueCircuits.Circuits

/-- Lemma 2, printed p.16 / PDF 17. The minimum is attained by an actual circuit;
there is no zero-valued empty-set minimum and no omitted block-summing factor. -/
theorem lemma_2 (R : Type) [CommRing R] (k ℓ : ℕ) (hk : 2 ≤ k) (hℓ : 0 < ℓ)
    (ns : Fin k → ℕ) (hns : ∀ i, ℓ ≤ ns i) :
    ∃ base : Circuit R (UniformVar k ℓ) 1,
      base.polynomial id 0 = uniformHypercliqueOver R k ℓ ∧
      complexityOver (uniformHypercliqueOver R k ℓ) = (base.size : WithTop ℕ) ∧
      ∃ c : Circuit R (HVar ns) 1,
        c.polynomial id 0 = hypercliqueOver R ns ∧
        c.size ≤ base.size * ∏ i : Fin k, ((ns i + ℓ - 1) / ℓ) := by sorry

end HypercliqueCircuits.Circuits
