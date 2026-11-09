-- Prove2me | Theorems.Thm_MultiplierAssoc206_Resolution_proposition_4_6
-- name    : MultiplierAssoc206.Resolution.proposition_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:18:16.751314+00:00
-- url     : https://prove2.me/theorems/0e501543-4eab-4413-aa4c-c29eff48ee9c
-- title:
--   The array multiplier encoding is strip-local
-- statement:
--   The family of $n$-bit array multipliers of Figure 1, each encoded gate by gate as a CNF, is strip-local (Definition 4.3): every member is an exact multiplier encoding (Definition 2.3), all its clauses have width at most $4$, and for every $g\ge1$ and every $g$-sparse restriction of the inputs every wire is a Boolean function of the partial products of a single $g$-strip.
--
--   Together with Proposition 4.7 it shows that the class of strip-local encodings, to which Theorem 8.8 applies, contains the standard multipliers.
--
--   Differences from the source:
--   - reading: the array multiplier encoding (Figure 1); strip-local is defined for exact encodings → the circuit of Figure 1 with its row-0, first-box and diagonal-arrow conventions, each gate encoded by one clause per assignment of its inputs; exactness is part of the conclusion; reason: the paper fixes the multiplier only by Figure 1 and no particular clause set; it asserts exactness on PDF p.5 ('Observe that this is an exact multiplier encoding') and width at most four in the proof
-- source:
--   Vincent Liew, Associativity of Multiplication Is Hard for Resolution, STOC 2027 submission #206 (October 2026), source.pdf SHA-256 676dcc4be9158c52d07aec1c9d48f53fa38289ed1b4dcb34b53adc70dbdd5ead, PDF p.7 (printed p.6), Proposition 4.6 (array multiplier: §2 and Figure 1, PDF pp.5–6)

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_ArrayMultiplier

namespace MultiplierAssoc206.Resolution

/-- Proposition 4.6, PDF p.7 (printed p.6): the array multiplier encoding (Figure 1) is
strip-local (including exact, Definition 2.3). -/
theorem proposition_4_6 : StripLocal arrayMultiplier := by sorry

end MultiplierAssoc206.Resolution
