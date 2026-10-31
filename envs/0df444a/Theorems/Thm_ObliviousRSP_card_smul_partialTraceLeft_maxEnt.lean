-- Prove2me | Theorems.Thm_ObliviousRSP_card_smul_partialTraceLeft_maxEnt
-- name    : ObliviousRSP.card_smul_partialTraceLeft_maxEnt
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:21:50.241444+00:00
-- url     : https://prove2.me/theorems/2bcd7855-edc5-4a6d-bf70-8705a5b4b25b
-- title:
--   Identity $d\,\operatorname{Tr}_1[\varphi^T_1|\Phi_d\rangle\langle\Phi_d|_{12}] = \varphi$
-- statement:
--   For every operator $\varphi$ on $\mathbb C^d$,
--   $$
--   d\,\operatorname{Tr}_1\big[(\varphi^{T}\otimes I)\,|\Phi_d\rangle\langle\Phi_d|\big] = \varphi ,
--   $$
--   where $\operatorname{Tr}_1$ traces out the first factor and $\varphi^T$ is the transpose.
--
--   This "transpose trick" moves an operator from one half of the maximally entangled state to the other; the paper uses it to obtain (11).
--
--   **Formalization Note** $\operatorname{Tr}_1$ is `WildeQIT.partialTraceLeft` and $d$ is the number of basis indices; for a zero-dimensional space both sides are the empty matrix.
--
--   Differences from the source:
--   - generalization: φ a pure state of the ensemble → any square matrix φ; reason: the identity is linear in φ and the page's states are matrices
-- source:
--   Leung–Shor, Oblivious remote state preparation, arXiv:quant-ph/0201008v1, p.4, identity used for eq. (11)

import Mathlib
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_ObliviousRSP_maxEnt

open scoped Kronecker Matrix

namespace ObliviousRSP

/-- Leung–Shor, *Oblivious remote state preparation*, arXiv:quant-ph/0201008v1, p.4, the identity used for eq. (11): "We trace out the first register and used
d Tr1 [ φ^T_1 |Φd⟩⟨Φd|12 ] = φ". For every operator `φ` on the input space,
`d · Tr_1[(φᵀ ⊗ I) |Φ_d⟩⟨Φ_d|] = φ`.

**Formalization Note.** Stated for every matrix `φ`, not only the pure states the page applies it
to. `Tr_1` is `WildeQIT.partialTraceLeft`, `d = Fintype.card ι`, `|Φ_d⟩⟨Φ_d|` is `maxEnt ι`; for an
empty `ι` both sides are the empty matrix. -/
theorem card_smul_partialTraceLeft_maxEnt {ι : Type} [Fintype ι] [DecidableEq ι]
    (φ : Matrix ι ι ℂ) :
    (Fintype.card ι : ℂ) • WildeQIT.partialTraceLeft ((φᵀ ⊗ₖ (1 : Matrix ι ι ℂ)) * maxEnt ι) =
      φ := by sorry

end ObliviousRSP
