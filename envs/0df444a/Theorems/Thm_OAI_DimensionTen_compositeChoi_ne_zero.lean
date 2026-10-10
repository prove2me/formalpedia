-- Prove2me | Theorems.Thm_OAI_DimensionTen_compositeChoi_ne_zero
-- name    : OAI.DimensionTen.compositeChoi_ne_zero
-- status  : Proved
-- author  : @elem
-- created : 2026-10-10T10:57:05.836476+00:00
-- url     : https://prove2.me/theorems/0317f91d-fd2b-43e0-833d-72d90ba5d394
-- title:
--   The composite Choi matrix $Z = J(\Phi_2 \circ \Phi_1)$ is nonzero
-- statement:
--   The Choi matrix $Z = J(\Phi_2 \circ \Phi_1)$ of the composition of the two explicit maps of the dimension-ten pair, a $100 \times 100$ matrix whose $((u_1,u_2),(v_1,v_2))$ entry is $\big(\Phi_2(\Phi_1(E_{u_1 v_1}))\big)_{u_2 v_2}$, is not the zero matrix. Concretely its top-left entry equals $6 \cdot 1296^2 = 10{,}077{,}696$, because $\Phi_1(E_{00}) = 1296\, E E^*$ and $\Phi_2$ then returns $1296\,\operatorname{tr}\big(R(E_{00})\big)$ in that entry.
-- source:
--   OpenAI, Entanglement with zero distillable secret key in local dimension ten (September 27, 2026), https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf, Section 6, proof of Proposition 6.1 (the positive definite output of L makes Z nonzero) and Section 7, equation (7.1).

import Mathlib
import Definitions.Def_DimensionTenPair

open Matrix Complex
open scoped Matrix ComplexOrder

namespace OAI.DimensionTen

theorem compositeChoi_ne_zero : choi (phiTwo ∘ phiOne) ≠ 0 := by sorry

end OAI.DimensionTen
