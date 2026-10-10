-- Prove2me | Theorems.Thm_OAI_DimensionTen_phiOne_ppt
-- name    : OAI.DimensionTen.phiOne_ppt
-- status  : Open
-- author  : @elem
-- created : 2026-10-10T10:58:49.210186+00:00
-- url     : https://prove2.me/theorems/7abd62fb-0f48-4115-8549-52c00462f4aa
-- title:
--   The map $\Phi_1$ of the dimension-ten pair is PPT
-- statement:
--   The explicit map $\Phi_1 : M_{10}(\mathbb C) \to M_{10}(\mathbb C)$ of the source, $\Phi_1(A) = E\, S(A^{T})\, E^*$ where $S(A) = V^*(L \otimes L)(U A U^*) V$ is built from the integer pencil map $L$, the symmetric isometry $U$, the exterior isometry $V$ and the coordinate inclusion $E : \mathbb C^6 \to \mathbb C^{10}$, is PPT: it is complex linear, completely positive, and its output transpose $A \mapsto \Phi_1(A)^T$ is completely positive. Complete positivity is taken in the amplification sense: for every $k \ge 1$, applying the map to the second factor of a positive semidefinite matrix on $\mathbb C^k \otimes \mathbb C^{10}$ gives a positive semidefinite matrix.
-- source:
--   OpenAI, Entanglement with zero distillable secret key in local dimension ten (September 27, 2026), https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf, Section 6, equation (6.5) and the paragraph following it (PPT property of Φ₁ via Lemma 2.1); Section 7, Lemma 7.1 (the pencil map L is PPT).

import Mathlib
import Definitions.Def_DimensionTenPair

open Matrix Complex
open scoped Matrix ComplexOrder

namespace OAI.DimensionTen

theorem phiOne_ppt : PPT phiOne := by sorry

end OAI.DimensionTen
