-- Prove2me | Theorems.Thm_MetricMSO_cbl_polytime
-- name    : MetricMSO.cbl_polytime
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:45:39.96069+00:00
-- url     : https://prove2.me/theorems/d87378ea-9719-40e4-a8ac-fc996c78763b
-- title:
--   §2.2 — $\mathrm{cbl}(G)$ is computable in polynomial time
-- statement:
--   There are a Turing machine and a constant $c$ such that, for every finite graph $G$, given the adjacency-matrix code of $G$, the machine outputs $\mathrm{cbl}(G)$ in binary within time polynomial in the input length:
--   $$\text{time}\le(\text{length}+1)^c.$$
--
--   This is the first step of the proof of the goal: from $\mathrm{cbl}(G)$ one obtains the modulus $M:=\max\{3,\mathrm{cbl}(G)+1\}$.
--
--   Differences from the source:
--   - encoding: the running time of an unspecified algorithm, including arithmetic and writing the output → the published OutputsWithin: a Mathlib multi-stack Turing machine (TM2) halting with the output within t steps; reason: time classes f(k)N^{O(1)} are closed under polynomial simulation, so the machine model does not change the statement
--   - encoding: polynomial time → (length + 1)^c for one c over all graphs; reason: the input length is at least 1
--   - encoding: a graph G → encodeGraph, an adjacency matrix preceded by n in binary; reason: any two standard graph encodings have polynomially related lengths
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c586330b037548a2b4a977081284996698f39c1b55c17b91cb81a536d3dd9), §2.2, p.13 (PDF 15), the sentence after Lemma 2.1; proof of Theorem 1.1, p.29 (PDF 31)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_MetricMSO_encodeInput
import Definitions.Def_MetricMSO_cbl

open HMBinPacking (OutputsWithin)
open ExponomialAssortment.FPTAS (encodeNat)

namespace MetricMSO

/-- **`cbl(G)` is computable in polynomial time.** Chakraborty, Ordyniak, Siebertz (arXiv:2610.41974, sha256 prefix ad3c5863), §2.2, p.13
(PDF 15), the sentence after Lemma 2.1: "Thus cbl(G) can be computed in polynomial time." Repeated in
the proof of Theorem 1.1, p.29 (PDF 31): "By Horton's algorithm and Lemma 2.1, we can compute cbl(G)
in polynomial time [Hor87]."

**Formalization Note** One machine for all graphs on `Fin n`; the input is the adjacency-matrix code
`encodeGraph G`, the output `cbl(G)` in binary, and the bound is `(length + 1)^c`. -/
theorem cbl_polytime :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (c : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      OutputsWithin M (encodeGraph G) (encodeNat (cbl G)) (((encodeGraph G).length + 1) ^ c) := by sorry

end MetricMSO
