-- Prove2me | Theorems.Thm_HypercliqueCircuits_Circuits_lemma_3
-- name    : HypercliqueCircuits.Circuits.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T00:35:46.901647+00:00
-- url     : https://prove2.me/theorems/d3951e1c-49c3-4c54-9343-8ce33c979d5e
-- title:
--   Lemma 3 — all derivatives in at most four times the size
-- statement:
--   There is one absolute positive constant $C$ such that, over every commutative ring, a fixed finite transformation program takes any circuit of size $s$ for a polynomial $P(x_1,\ldots,x_n)$ and returns a circuit computing all first formal partial derivatives. Its output satisfies
--
--   $$|C'|\le4s,\qquad T_{\rm records}\le Cs,\qquad C'_i=\frac{\partial P}{\partial x_i}\quad(i\in[n]).$$
--
--   Time counts actual machine transitions on gate records, coefficient atoms and pointers. All declared inputs are counted among the input circuit's vertices. The transformation's output is a complete circuit with the same coefficient type; no external infinite constant table is used. This is the timed differentiation tool needed by the contraction computation and the uniform goal.
--
--   Differences from the source:
--   - generalization: arithmetic circuits in the source coefficient setting → circuits with arbitrary literal coefficients over every commutative ring; reason: the division-free identities apply over these rings and specialize to the dyadic source setting
--   - reading: arithmetic circuit size without a leaf-count convention → total vertices, including all declared variable sources and literal constant sources; output pointers are free; reason: fixes one size convention for every result; sharing and exact factors are audited in MODERATION_NOTES.md
--   - encoding: one-based coordinate tuples and deletion of position j → Fin coordinates and functions on the ordered subtype of positions other than j; reason: the increasing-coordinate bijection preserves all variables and every monomial
--   - reading: construction in O(s) time → one finite coefficient-copying record RAM per ring, with an absolute linear transition bound; reason: makes the source gate-record operation convention explicit; bit serialization is charged separately in the goal
-- source:
--   Josh Alman, Baitian Li, Neha Pant, Kevin Pratt, Ryan Williams, Finding Hypercliques Faster Than Brute Force, STOC 2027 submission #1224 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1224.pdf, Lemma 3 ([BS83; Mor85]), p.16 (PDF 17).

import Definitions.Def_HypercliqueCircuits_Circuits_Transpose
import Definitions.Def_HypercliqueCircuits_Circuits_Machine

set_option autoImplicit false

namespace HypercliqueCircuits.Circuits

/-- Lemma 3, printed p.16 / PDF 17. O(s) is a word/record operation count.
The opaque atoms are the finite coefficients serialized in this input circuit, not a free table. -/
theorem lemma_3 :
    ∃ C : ℕ, 0 < C ∧ ∀ (R : Type) [CommRing R], ∃ prog : Program R,
      ∀ n : ℕ, ∀ c : Circuit R (Fin n) 1,
        ∃ t : ℕ, ∃ out : Circuit R (Fin n) n,
          (execute prog (derivativeInput c) t).halted = true ∧
          (execute prog (derivativeInput c) t).output = derivativeOutput out ∧
          t ≤ C*c.size ∧ out.size ≤ 4*c.size ∧
          ∀ i : Fin n, out.polynomial id i =
            MvPolynomial.pderiv i (c.polynomial id 0) := by sorry

end HypercliqueCircuits.Circuits
