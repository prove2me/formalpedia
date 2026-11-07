-- Prove2me | Theorems.Thm_LDPSelect_minor_minimal
-- name    : LDPSelect.minor_minimal
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:55:57.311641+00:00
-- url     : https://prove2.me/theorems/fb60b851-79e1-4708-9e2b-2fe06150c53a
-- title:
--   A.7, minor-minimal families — a minimal family outside $\mathcal G$ is some $O_i$ or some $B_m$, $m\ge4$
-- statement:
--   Let $H$ be a downward-closed family that is not in $\mathcal G$ while all its proper minors are. Then $H$ is isomorphic to one of $O_1,\dots,O_9$ or to $B_m$ for some $m\ge4$.
--
--   Differences from the source:
--   - encoding: minors by repeated contraction and deletion, up to isomorphism → one contraction of a feasible set followed by one deletion, with an injective relabelling; reason: the paper's own reduction (§3.4, p.8): (F∖D)/I = (F/I)∖D
--   - encoding: a proper minor → a minor on fewer elements; reason: a minor on as many elements is H itself up to isomorphism
-- source:
--   Chen, Wang, When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy, STOC 2027 submission (manuscript sha256 2e2d6157…), A.7, Minor-minimal families, p.20 (pdf p.21)

import Mathlib
import Definitions.Def_LDPSelect_InClass
import Definitions.Def_LDPSelect_IsMinorOf
import Definitions.Def_LDPSelect_Obstructions

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LDPSelect

/-- Chen, Wang, *When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy*, STOC 2027 submission (manuscript sha256 2e2d6157…), A.7, p.20, Minor-minimal families.

A family outside `G` all of whose proper minors lie in `G` is isomorphic to some `O_i` or some `B_m`
with `m ≥ 4`.

**Formalization Note.** A proper minor is a minor on fewer elements: a minor on the same number of
elements has `I = ∅` and a bijective embedding, so it is `H` itself. -/
theorem minor_minimal {n : ℕ} (H : Family n) (hH : IsDownClosed H) (hG : ¬ InClass H)
    (hmin : ∀ (k : ℕ) (O : Family k), k < n → IsMinorOf O H → InClass O) :
    (∃ i, IsIsoFam (O i) H) ∨ ∃ m, 4 ≤ m ∧ IsIsoFam (B m) H := by sorry

end LDPSelect
