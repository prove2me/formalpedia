-- Prove2me | Theorems.Thm_MultibrotCorr_lemma_5_3
-- name    : MultibrotCorr.lemma_5_3
-- status  : Open
-- author  : @LG
-- created : 2026-11-20T23:34:51.083371+00:00
-- url     : https://prove2.me/theorems/bfd74f54-beaa-48c9-b508-caeaefd87da1
-- title:
--   Lemma 5.3 — the total filled Julia set is closed in $\mathbb{C}^2$
-- statement:
--   Let $K$ denote the set of all $(c,z)\in\mathbb{C}^2$ such that $z\in K_c$. Then $K$ is closed. This is the parameter-space closedness of the total filled Julia set, used to apply Tan Lei's theorem.
-- source:
--   C. Siqueira, Similarity between the Multibrot set and the Julia set of correspondences at Misiurewicz points, https://arxiv.org/abs/2509.07266, Lemma 5.3, Section 5.

import Mathlib
import Definitions.Def_mcorr_branches

open Set Filter Topology Finset

namespace MultibrotCorr
theorem lemma_5_3 (e : UnicriticalExponent) :
    IsClosed {p : ℂ × ℂ | p.2 ∈ filledJulia e p.1} := by sorry
end MultibrotCorr
