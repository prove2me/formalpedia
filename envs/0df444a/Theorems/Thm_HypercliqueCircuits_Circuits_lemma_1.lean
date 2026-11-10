-- Prove2me | Theorems.Thm_HypercliqueCircuits_Circuits_lemma_1
-- name    : HypercliqueCircuits.Circuits.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T00:35:37.919545+00:00
-- url     : https://prove2.me/theorems/9e6ff400-7997-4c84-a45e-8edee88003bf
-- title:
--   Lemma 1 — rectangular matrix multiplication
-- statement:
--   There are absolute constants $\gamma\ge1/8$ and $C>0$ such that, for all positive $n_1,n_2,n_3$, one circuit computes every entry of the product of independent $n_1\times n_2$ and $n_2\times n_3$ input matrices, with
--
--   $$|C_{n_1,n_2,n_3}|\le C(n_1n_2n_3)\min(n_1,n_2,n_3)^{-\gamma}.$$
--
--   The constants are chosen before the dimensions and coefficient ring. The outputs are formal polynomial entries, rather than evaluations on bounded inputs. This is the rectangular circuit tool used by the low-degree bound.
--
--   Differences from the source:
--   - generalization: arithmetic circuits in the source coefficient setting → circuits with arbitrary literal coefficients over every commutative ring; reason: the division-free identities apply over these rings and specialize to the dyadic source setting
--   - reading: arithmetic circuit size without a leaf-count convention → total vertices, including all declared variable sources and literal constant sources; output pointers are free; reason: fixes one size convention for every result; sharing and exact factors are audited in MODERATION_NOTES.md
--   - encoding: one-based coordinate tuples and deletion of position j → Fin coordinates and functions on the ordered subtype of positions other than j; reason: the increasing-coordinate bijection preserves all variables and every monomial
--   - encoding: O bounds with fixed parameters and changing dimensions → positive constants quantified before every changing dimension and subset, with all positive sizes covered; reason: finite small sizes can be absorbed in a constant depending only on the displayed fixed parameters
-- source:
--   Josh Alman, Baitian Li, Neha Pant, Kevin Pratt, Ryan Williams, Finding Hypercliques Faster Than Brute Force, STOC 2027 submission #1224 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1224.pdf, Lemma 1, p.16 (PDF 17).

import Definitions.Def_HypercliqueCircuits_Circuits_Transpose
import Definitions.Def_HypercliqueCircuits_Circuits_Machine

set_option autoImplicit false

namespace HypercliqueCircuits.Circuits

/-- Lemma 1, printed p.16 / PDF 17. The constants precede every changing dimension. -/
theorem lemma_1 :
    ∃ γ C : ℝ, 1/8 ≤ γ ∧ 0 < C ∧ ∀ (R : Type) [CommRing R], ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
      ∃ circ : Circuit R (MMVar a b c) (a*c),
        (∀ i : Fin a, ∀ j : Fin c,
          circ.polynomial id (finProdFinEquiv (i,j)) = matrixProduct R a b c i j) ∧
        (circ.size : ℝ) ≤ C * (a*b*c : ℕ) * (min a (min b c) : ℝ) ^ (-γ) := by sorry

end HypercliqueCircuits.Circuits
