-- Prove2me | Theorems.Thm_MultiplierAssoc206_Resolution_proposition_4_7
-- name    : MultiplierAssoc206.Resolution.proposition_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:23:07.13075+00:00
-- url     : https://prove2.me/theorems/83b9bbfc-ee23-4d2d-a815-8b5779be249a
-- title:
--   The Wallace-tree multiplier with a carry-lookahead adder is strip-local
-- statement:
--   The family of standard $n$-bit Wallace-tree multipliers (Definition A.2), whose final two rows are summed by a carry-lookahead adder (Definition A.1), each encoded gate by gate as a CNF, is strip-local (Definition 4.3): every member is an exact multiplier encoding, its clauses have width bounded by a constant independent of $n$, and for every $g\ge1$ and every $g$-sparse restriction of the inputs every wire is a Boolean function of the partial products of a single $g$-strip.
--
--   Strip-locality fails for Wallace trees if the sparsity threshold $2^{g-1}$ is replaced by $2^g$ (Remark 4.4).
--
--   Differences from the source:
--   - reading: the standard Wallace-tree multiplier (Definition A.2) with a carry-lookahead adder (Definition A.1) → the layer construction with adders A_{ℓ,i,J} appended for J = 0, 1, … and columns in increasing order, a pass-through adder emitting no carry, ℓ_max the first layer with at most two rows, and a 4^L-bit CLA (4^L ≥ 2n, constant-0 padding) with wires p_i, q_i, group pairs through the root level, carries through the final carry-out, and all padded sum bits; each gate encoded by one clause per assignment of its inputs; exactness is part of the conclusion; reason: the definitions leave these details open; the choices reproduce the stated row count ⌈2N/3⌉ and the four wire types of the proof of Lemma A.5, and Observation A.3 asserts exactness
-- source:
--   Vincent Liew, Associativity of Multiplication Is Hard for Resolution, STOC 2027 submission #206 (October 2026), source.pdf SHA-256 676dcc4be9158c52d07aec1c9d48f53fa38289ed1b4dcb34b53adc70dbdd5ead, PDF p.8 (printed p.7), Proposition 4.7 (Definitions A.1, A.2 on PDF pp.26–28; proof PDF p.30)

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_Wallace

namespace MultiplierAssoc206.Resolution

/-- Proposition 4.7, PDF p.8 (printed p.7; proof PDF p.30): the standard Wallace-tree
multiplier encoding (Definition A.2), whose final two rows are summed by a carry-lookahead adder
(Definition A.1), is strip-local (including exact, Observation A.3). -/
theorem proposition_4_7 : StripLocal wallaceMultiplier := by sorry

end MultiplierAssoc206.Resolution
