-- Prove2me | Theorems.Thm_OAI_DimensionTen_not_entanglementBreaking_of_range_criterion
-- name    : OAI.DimensionTen.not_entanglementBreaking_of_range_criterion
-- status  : Proved
-- author  : @elem
-- created : 2026-10-10T10:56:34.938429+00:00
-- url     : https://prove2.me/theorems/cc557541-877c-4a81-b604-f70f436e8ee7
-- title:
--   Range criterion: a nonzero Choi matrix with no product vector in its range is not entanglement breaking
-- statement:
--   Let $F : M_a(\mathbb C) \to M_b(\mathbb C)$ be any map (no linearity is assumed in the statement) whose Choi matrix $J(F) = \big(F(E_{ij})\big)_{ij}$ on $\mathbb C^a \otimes \mathbb C^b$ is nonzero and whose range contains no nonzero product vector: whenever $J(F)\,w = u \otimes v$ for some $w$, then $u = 0$ or $v = 0$. Then $F$ is not entanglement breaking in the amplification sense of the mission: it is not the case that $F$ is completely positive and $(\mathrm{id}_k \otimes F)(X)$ is separable for every positive semidefinite $X$ on $\mathbb C^k \otimes \mathbb C^a$ and every $k \ge 1$.
--
--   This is the range criterion of P. Horodecki in the form used in the proof of Theorem 1.2 of the source: an entanglement-breaking map has a separable Choi matrix (apply the amplification to the unnormalized maximally entangled matrix $\Omega = \sum_{i,j} E_{ij} \otimes E_{ij}$), and a nonzero separable matrix $\sum_i A_i \otimes B_i$ with $A_i, B_i \succeq 0$ has a nonzero product vector $(A_i x) \otimes (B_i y)$ in its range, because the range of a sum of positive semidefinite matrices contains the range of each summand.
-- source:
--   OpenAI, Entanglement with zero distillable secret key in local dimension ten (September 27, 2026), https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf, Section 1 (Theorem 1.2, final sentence) and Section 6, proof of Proposition 6.1 (range step); P. Horodecki, Phys. Lett. A 232 (1997) 333, range criterion.

import Mathlib
import Definitions.Def_DimensionTenPair

open Matrix Complex
open scoped Matrix ComplexOrder

namespace OAI.DimensionTen

theorem not_entanglementBreaking_of_range_criterion {a b : ℕ} (F : Mat a → Mat b)
    (hne : choi F ≠ 0)
    (hr : ∀ (u : Fin a → ℂ) (v : Fin b → ℂ) (w : Fin a × Fin b → ℂ),
      choi F *ᵥ w = productVector u v → u = 0 ∨ v = 0) :
    ¬ EntanglementBreaking F := by sorry

end OAI.DimensionTen
