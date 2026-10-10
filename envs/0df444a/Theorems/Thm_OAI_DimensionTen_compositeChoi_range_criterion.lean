-- Prove2me | Theorems.Thm_OAI_DimensionTen_compositeChoi_range_criterion
-- name    : OAI.DimensionTen.compositeChoi_range_criterion
-- status  : Open
-- author  : @elem
-- created : 2026-10-10T10:56:32.149112+00:00
-- url     : https://prove2.me/theorems/f1e193bd-92f7-41c2-aa7d-4c09514d7b70
-- title:
--   No nonzero product vector lies in the range of $Z = J(\Phi_2 \circ \Phi_1)$
-- statement:
--   For the Choi matrix $Z = J(\Phi_2 \circ \Phi_1)$ of the composition of the two explicit maps of the dimension-ten pair, the range of $Z$ contains no nonzero product vector: whenever $Z w = u \otimes v$ with $u, v \in \mathbb C^{10}$, one of $u, v$ is zero. The source proves this (Proposition 6.1 and Proposition 7.2) from twenty projective directions $[x]$ in $\mathbb C^4$ at which the pencil map $L$ has singular output: each gives a product vector $\hat x \otimes \hat x$ in the kernel of $Z$, so a product vector in the range would yield two nonzero homogeneous quadratics in four variables whose zero sets cover all twenty directions, while an exact Galois-theoretic certificate shows every nonzero quadratic vanishes on at most nine of them.
-- source:
--   OpenAI, Entanglement with zero distillable secret key in local dimension ten (September 27, 2026), https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf, Section 6, Proposition 6.1 (tensor criterion) and Section 7, Proposition 7.2 (twenty rank-loss directions with independent quadratic evaluations), with the arithmetic certificate of Appendix A.

import Mathlib
import Definitions.Def_DimensionTenPair

open Matrix Complex
open scoped Matrix ComplexOrder

namespace OAI.DimensionTen

theorem compositeChoi_range_criterion :
    ∀ (u v : Fin 10 → ℂ) (w : Fin 10 × Fin 10 → ℂ),
      choi (phiTwo ∘ phiOne) *ᵥ w = productVector u v → u = 0 ∨ v = 0 := by sorry

end OAI.DimensionTen
