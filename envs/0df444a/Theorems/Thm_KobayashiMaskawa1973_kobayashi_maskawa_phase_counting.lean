-- Prove2me | Theorems.Thm_KobayashiMaskawa1973_kobayashi_maskawa_phase_counting
-- name    : KobayashiMaskawa1973.kobayashi_maskawa_phase_counting
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T18:59:52.920101+00:00
-- url     : https://prove2.me/theorems/24078414-a91a-441d-b7bb-b6417e83e257
-- title:
--   Kobayashi--Maskawa phase counting: no $CP$-violating phase for four quarks, one surviving phase for six
-- statement:
--   This is the mathematical content of Kobayashi and Maskawa's argument, in one statement: the phase counting that distinguishes the four-quark from the six-quark scheme.
--
--   1. **Quartet scheme, Eq. (6).** Every $2\times2$ unitary mixing matrix can be brought, by a change of phase convention of the fields, to the real rotation
--   $$\begin{pmatrix}\cos\theta&\sin\theta\\-\sin\theta&\cos\theta\end{pmatrix}.$$
--   Hence in the quartet model (with $\mathcal L'=0$) the charged-current interaction can be made real and no $CP$ violation arises from it.
--
--   2. **Six-quark scheme, obstruction.** Some $3\times3$ unitary matrix admits no real representative in its rephasing orbit: "all phases of elements of a $3\times3$ unitary matrix cannot be absorbed into the phase convention of six fields".
--
--   3. **Six-quark scheme, normal form, Eq. (13).** Every $3\times3$ unitary matrix is rephasing equivalent to
--   $$
--   K(\theta_1,\theta_2,\theta_3,\delta)=
--   \begin{pmatrix}
--   c_1 & -s_1c_3 & -s_1s_3\\
--   s_1c_2 & c_1c_2c_3-s_2s_3e^{i\delta} & c_1c_2s_3+s_2c_3e^{i\delta}\\
--   s_1s_2 & c_1s_2c_3+c_2s_3e^{i\delta} & c_1s_2s_3-c_2c_3e^{i\delta}
--   \end{pmatrix},
--   $$
--   with three angles and a single residual phase $\delta$.
--
--   Together, (1)--(3) are the reason the paper proposes a third quark doublet: the surviving phase $\delta$ is the source of $CP$-violating interference among current components, and it has no analogue in the four-quark case.
--
--   **Formalization Note** Only the algebraic content is formalized. The paper's physical arguments (the fate of the pseudoscalar part of the mass term, the bound on strangeness-changing neutral currents, the $g_A/g_V$ constraints) are not part of this statement.
-- source:
--   M. Kobayashi and T. Maskawa, "CP-Violation in the Renormalizable Theory of Weak Interaction", Progress of Theoretical Physics 49 (1973) 652-657, https://doi.org/10.1143/PTP.49.652, pp. 654 Eq. (6) and the paragraph following it; pp. 657 Eq. (13) -- the algebraic content of the paper's phase-counting argument

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs

open Matrix

namespace KobayashiMaskawa1973

theorem kobayashi_maskawa_phase_counting :
    (∀ U ∈ Matrix.unitaryGroup (Fin 2) ℂ, ∃ θ : ℝ, RephasingEquiv U (cabibboMatrix θ)) ∧
    (∃ U ∈ Matrix.unitaryGroup (Fin 3) ℂ,
      ∀ V : Matrix (Fin 3) (Fin 3) ℂ, RephasingEquiv U V → ¬ IsRealMatrix V) ∧
    (∀ U ∈ Matrix.unitaryGroup (Fin 3) ℂ,
      ∃ θ₁ θ₂ θ₃ δ : ℝ, RephasingEquiv U (kmMatrix θ₁ θ₂ θ₃ δ)) := by sorry

end KobayashiMaskawa1973
