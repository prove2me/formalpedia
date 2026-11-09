-- Prove2me | Theorems.Thm_MWCSherali_theorem_1_1
-- name    : MWCSherali.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:14:23.696138+00:00
-- url     : https://prove2.me/theorems/cc96b01b-9834-4e3d-890c-1f22e0690808
-- title:
--   Theorem 1.1 — assuming UGC, Multiway Cut is NP-hard to approximate within $1.22232$
-- statement:
--   Assuming the Unique Games Conjecture, Multiway Cut is NP-hard to approximate within a factor of $1.22232$.
--
--   Precisely: there are $c>0$ and $s>1.22232\,c$ such that it is NP-hard to distinguish weighted Multiway Cut instances having a multiway cut of weight at most $cW$ from instances all of whose multiway cuts weigh at least $sW$, where $W>0$ is the total weight and the number of terminals is part of the input.
--
--   This improves the previous lower bound $1.20016$ of Bérczi, Chandrasekaran, Király and Madan for Multiway Cut with an arbitrary number of terminals.
--
--   Differences from the source:
--   - encoding: the Unique Games Conjecture [Kho02] (not stated in the paper) → OptInapprox.MaxCut.UGC: for all η, γ > 0 there is M such that Unique Label Cover with M labels is gap NP-hard for (1 − η, γ); reason: the standard statement of the conjecture, from a published module
--   - reading: "NP-hard to approximate within a factor of ρ" → gap NP-hardness: for some c > 0 and s > ρc, distinguishing instances with a multiway cut of weight ≤ cW from instances whose multiway cuts all weigh ≥ sW is NP-hard (W > 0, at least one terminal); reason: the standard meaning; a ρ-approximation algorithm decides this gap problem
--   - reading: weighted graphs with w : E → ℝ_+ → natural-number weights written as edge multiplicities (unary multigraph encoding); reason: hardness on this subclass implies hardness for rational or real weights under any reasonable encoding
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), Theorem 1.1, p.2

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_UGC
import Definitions.Def_MWCSherali_MWCHard

namespace MWCSherali

open OptInapprox.MaxCut

/-- **Theorem 1.1 (UG-hardness of Multiway Cut within 1.22232).** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3, 2026), Theorem 1.1,
p.2: "Assuming the Unique Games Conjecture, Multiway Cut is NP-hard to approximate within a
factor of 1.22232."

**Formalization Note.**
* `UGC` is the Unique Games Conjecture of the reused module `OptInapprox.MaxCut`.
* `MWCHard ρ` is gap NP-hardness of weighted Multiway Cut with ratio strictly above `ρ`: for some
  `0 < c` and `s > ρ c` it is NP-hard to tell instances with a multiway cut of weight `≤ c·W` from
  instances all of whose multiway cuts weigh `≥ s·W` (`W > 0` the total weight, at least one
  terminal). The number of terminals is part of the input (Table 1: "an arbitrary number of
  terminals"). Weights are unary multigraph multiplicities. -/
theorem theorem_1_1 : UGC → MWCHard (1.22232 : ℝ) := by sorry

end MWCSherali
