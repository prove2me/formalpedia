-- Prove2me | Theorems.Thm_ObliviousRSP_eq_6_8
-- name    : ObliviousRSP.eq_6_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:22:40.062989+00:00
-- url     : https://prove2.me/theorems/3cebe047-fec2-43e3-8ce4-68191d305945
-- title:
--   Eqs. (6)–(8) — Bob's state in the modified protocol in matrix units
-- statement:
--   For every operator $M_m$ on the specimen and Alice's half and every operator $\varphi$ on the input space, Bob's unnormalized state in the modified protocol,
--   $$
--   \mathbf b = \operatorname{Tr}_{12}\big[(\varphi_1\otimes|\Phi_{d'}\rangle\langle\Phi_{d'}|_{23})(M_{m,12}\otimes I_3)\big],
--   $$
--   equals
--   $$
--   \mathbf b = \sum_{j_1,j_2} \operatorname{Tr}\Big[\frac{1}{d'}\big(\varphi\otimes|j_1\rangle\langle j_2|\big)M_m\Big]\,|j_1\rangle\langle j_2| .
--   $$
--
--   This reduces $\mathbf b$ to traces on registers 1, 2, the form in which (9)–(13) compare it with $p_m\rho_{\varphi m}$.
--
--   **Formalization Note** $|j_1\rangle\langle j_2|$ is the matrix unit `Matrix.single j1 j2 1`. The intermediate line (7) is part of the proof.
--
--   Differences from the source:
--   - generalization: M_m the element (4) of the modified measurement and φ a prepared pure state → any operator M_m on ι × σ and any matrix φ; reason: (6)–(8) use no property of M_m or φ
-- source:
--   Leung–Shor, Oblivious remote state preparation, arXiv:quant-ph/0201008v1, eqs. (6)–(8), p.4

import Mathlib
import Definitions.Def_ObliviousRSP_modifiedBobState

open scoped Kronecker

namespace ObliviousRSP

/-- Leung–Shor, *Oblivious remote state preparation*, arXiv:quant-ph/0201008v1, eqs. (6)–(8), p.4: "Evaluating b, b = Tr12 [ ( φ1 ⊗ |Φd′⟩⟨Φd′|23 ) ( Mm12 ⊗ I3 ) ]
= ∑j1,j2 Tr12 [ 1/d′ ( φ1 ⊗ |j1⟩⟨j2|2 ⊗ |j1⟩⟨j2|3 ) ( Mm12 ⊗ I3 ) ]
= ∑j1,j2 Tr [ 1/d′ ( φ ⊗ |j1⟩⟨j2| ) Mm ] |j1⟩⟨j2|." For every operator `M_m` on the specimen and
Alice's half and every `φ`, Bob's unnormalized state in the modified protocol is
**b** `= ∑_{j1,j2} (1/d′) Tr[(φ ⊗ |j1⟩⟨j2|) M_m] |j1⟩⟨j2|`.

**Formalization Note.** **b** is `modifiedBobState Mm φ` (the right side of (6)); `|j1⟩⟨j2|` is
`Matrix.single j1 j2 1`; `d′ = Fintype.card σ`. The intermediate line (7) is proof. -/
theorem eq_6_8 {ι σ : Type} [Fintype ι] [Fintype σ] [DecidableEq σ]
    (Mm : Matrix (ι × σ) (ι × σ) ℂ) (φ : Matrix ι ι ℂ) :
    modifiedBobState Mm φ =
      ∑ j1 : σ, ∑ j2 : σ,
        ((Fintype.card σ : ℂ)⁻¹ * ((φ ⊗ₖ Matrix.single j1 j2 (1 : ℂ)) * Mm).trace) •
          Matrix.single j1 j2 (1 : ℂ) := by sorry

end ObliviousRSP
