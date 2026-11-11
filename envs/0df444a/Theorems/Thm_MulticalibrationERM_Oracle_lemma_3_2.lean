-- Prove2me | Theorems.Thm_MulticalibrationERM_Oracle_lemma_3_2
-- name    : MulticalibrationERM.Oracle.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:50:45.120842+00:00
-- url     : https://prove2.me/theorems/32fbb8a7-f72e-4d82-88bc-85d3b8e1c902
-- title:
--   Lemma 3.2 — the Hadamard tests have distortion √m
-- statement:
--   For every $m\ge1$, the list $S_{\mathrm{Had}}$ of the $\nu=2^{\lceil\log_2m\rceil}$ rows of the first $m$ columns of the Sylvester matrix $W_\nu$, followed by their negations, has distortion $\sqrt m$: it is nonempty, its entries lie in $[-1,1]$, $\sqrt m\ge1$, and
--   $$\|b\|_1\le\sqrt m\,\max_{\sigma\in S_{\mathrm{Had}}}\langle\sigma,b\rangle\qquad\text{for every }b\in\mathbb R^m.$$
--
--   Differences from the source:
--   - encoding: tests indexed by the grid Λ of size m → tests indexed by Fin m, for every m ≥ 1; reason: the paper notes (p. 16) that the definition and the construction apply verbatim to any finite index set of size m
-- source:
--   Okoroafor, The Sample Complexity of Multicalibration with an ERM Oracle, supplied 61-page preprint (PDF SHA256 654c7a8127547d76c5a4b6db236ce672c2c09a70d21d56a3981583e1805d0f8d; exact arXiv revision unresolved, not arXiv:2610.14363v1), p. 17, Lemma 3.2 (construction p. 16)

import Mathlib
import Definitions.Def_MulticalibrationERM_Oracle_Setting
import Definitions.Def_MulticalibrationERM_Oracle_Forecast

namespace MulticalibrationERM.Oracle

/-- Lemma 3.2 (p. 17): the Hadamard tests `S_Had` (rows of the first `m` columns of the
Sylvester matrix `W_ν`, `ν = 2^{⌈log₂ m⌉}`, and their negations) have distortion `√m`. -/
theorem lemma_3_2 (m : ℕ) (hm : 1 ≤ m) : HasDistortion (hadamardTests m) (Real.sqrt m) := by sorry

end MulticalibrationERM.Oracle
