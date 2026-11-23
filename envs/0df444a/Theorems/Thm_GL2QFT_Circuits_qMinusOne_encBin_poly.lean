-- Prove2me | Theorems.Thm_GL2QFT_Circuits_qMinusOne_encBin_poly
-- name    : GL2QFT.Circuits.qMinusOne_encBin_poly
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:48:20.852945+00:00
-- url     : https://prove2.me/theorems/2cfaaaed-c234-48ea-a302-22d8a2e0e786
-- title:
--   Polynomial-time binary encoding of $q-1$
-- statement:
--   For every choice $D$ of the field data $(p,r,f,F,h)$, the order $q-1=p^r-1$ of $\mathbb F_q^\times$ is computable in polynomial time from the binary code of $D$: one polynomial-time string function $f$ satisfies $f(D.\mathrm{encData})=\mathrm{encBin}(q-1)$ for every $D$.
--
--   This classical arithmetic interface instantiates the uniform cyclic Fourier-transform circuit at modulus $N=q-1$, as required by the multiplicative field transform $\mathfrak F_\times$ in Lemma 6.8(120). Polynomial time is measured in the length of the binary encoding of $D$, and $f$ is total on all binary strings.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols (2026), Quantum Fourier transform toolbox, arXiv:2608.28573, Remark 6.3 (p.34) and Lemma 6.8 eq. (120) (p.41)

import Definitions.Def_GL2QFT_Circuits_Leaves

open Classical
open GL2QFT GL2QFT.Supplement GL2QFT.Supplement.TotalA GL2QFT.Supplement.AGammaGates QAlgorithms QAlgorithms.Complexity

theorem GL2QFT.Circuits.qMinusOne_encBin_poly : ∃ f : Str → Str, PolyTimeComputable f ∧ ∀ D : FieldData, f D.encData = LocalHamiltonian.encBin (D.q - 1) := by sorry
