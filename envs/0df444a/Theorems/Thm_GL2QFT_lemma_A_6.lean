-- Prove2me | Theorems.Thm_GL2QFT_lemma_A_6
-- name    : GL2QFT.lemma_A_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:17:09.519275+00:00
-- url     : https://prove2.me/theorems/92c500ad-fdb5-4f2a-a735-c0fab35e2d52
-- title:
--   Lemma A.6 — Davenport–Hasse lifting: $g_{q^2}(\chi_\alpha\circ N)=-(g_q(\alpha))^2$
-- statement:
--   For every character $\chi_\alpha$ of $\mathbb F_q^*$, including the trivial one,
--   $$g_{q^2}(\chi_\alpha\circ N)=-\bigl(g_q(\alpha)\bigr)^2,$$
--   where $N:\mathbb F_{q^2}^*\to\mathbb F_q^*$ is the norm.
--
--   This is the case $n=2$ of the Davenport–Hasse lifting theorem; it identifies the decomposable characters' contribution in the A-block.
--
--   Differences from the source:
--   - encoding: $\alpha\in X_q$ → exponent label in $\mathbb Z/(q-1)\mathbb Z$; reason: Remark 6.2
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573 (held version, sha256 ecd45073…), Lemma A.6, eq. (275), p.80 (PDF p.81)

import Definitions.Def_GL2QFT_Characters

open Classical

namespace GL2QFT

open FieldData

/-- arXiv:2608.28573 (held version, sha256 ecd45073…), **Lemma A.6** (Davenport–Hasse lifting
equation), p.80 (PDF p.81): "For every `α ∈ X_q`, `g_{q²}(χ_α ∘ N) = −(g_q(α))²` (275)." All labels
`α`, including the trivial one. -/
theorem lemma_A_6 (D : FieldData) (α : D.Lab) :
    D.gaussQ2 (fun z => D.chi α (D.nrm z)) = -(D.gauss α) ^ 2 := by sorry

end GL2QFT
