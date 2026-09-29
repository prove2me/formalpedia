-- Prove2me | Theorems.Thm_KobayashiMaskawa1973_exists_unitary_three_not_rephasable_real
-- name    : KobayashiMaskawa1973.exists_unitary_three_not_rephasable_real
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T17:59:06.734201+00:00
-- url     : https://prove2.me/theorems/a3d661b8-d91c-495b-ae50-65533ac4ed43
-- title:
--   Some $3\times3$ unitary matrix cannot be made real by any phase convention
-- statement:
--   Kobayashi and Maskawa observe that the argument eliminating $CP$ violation in the quartet model "does not hold when we introduce one more fermion doublet with the same charge assignment. This is because all phases of elements of a $3\times3$ unitary matrix cannot be absorbed into the phase convention of six fields."
--
--   Formally: there exists a matrix $U\in\mathrm U(3)$ such that **no** matrix obtained from $U$ by a change of phase convention,
--   $$V=\operatorname{diag}(e^{ia_1},e^{ia_2},e^{ia_3})\;U\;\operatorname{diag}(e^{ib_1},e^{ib_2},e^{ib_3}),$$
--   has all entries real.
--
--   This is the existence half of the paper's central observation, and the reason a six-quark model can violate $CP$ while a four-quark model (with $\mathcal L'=0$) cannot: a phase that survives every rephasing produces relative phases between current components, and hence $CP$-violating interference.
--
--   **Formalization Note** The statement asserts existence of one such $U$; it does not claim that a generic $3\times3$ unitary matrix has this property, nor does it quantify the residual phase.
-- source:
--   M. Kobayashi and T. Maskawa, "CP-Violation in the Renormalizable Theory of Weak Interaction", Progress of Theoretical Physics 49 (1973) 652-657, https://doi.org/10.1143/PTP.49.652, pp. 654, final paragraph of section i) Case (A, C): 'all phases of elements of a 3x3 unitary matrix cannot be absorbed into the phase convention of six fields'

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs

open Matrix

namespace KobayashiMaskawa1973

theorem exists_unitary_three_not_rephasable_real :
    ∃ U ∈ Matrix.unitaryGroup (Fin 3) ℂ,
      ∀ V : Matrix (Fin 3) (Fin 3) ℂ, RephasingEquiv U V → ¬ IsRealMatrix V := by sorry

end KobayashiMaskawa1973
