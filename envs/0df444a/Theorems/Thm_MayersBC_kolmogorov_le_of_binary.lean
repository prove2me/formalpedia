-- Prove2me | Theorems.Thm_MayersBC_kolmogorov_le_of_binary
-- name    : MayersBC.kolmogorov_le_of_binary
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:57:25.485798+00:00
-- url     : https://prove2.me/theorems/0e59cba3-de0a-48b0-9056-169ad1331a22
-- title:
--   Section d, pp.7–8 — if $K \le 4\varepsilon$ for binary measurements, then for all measurements
-- statement:
--   Let $\rho_0, \rho_1$ be density matrices and $\varepsilon$ a real number. Suppose that every two-outcome measurement $\{Q, I-Q\}$ gives outcome distributions with Kolmogorov distance $K \le 4\varepsilon$. Then every measurement $\{M_j\}_{j\in J}$, with any finite set of outcomes $J$, gives outcome distributions $p_b(j) = \operatorname{Tr}(M_j\rho_b)$ with
--
--   $$
--   K(p_0, p_1) = \sum_{j \in J} |p_0(j) - p_1(j)| \le 4\varepsilon .
--   $$
--
--   Differences from the source:
--   - encoding: operators M_j^(B) = P_j U, U an isometry and P_j projections (refs [6,14]) → POVM elements M_j (IsPOVM) indexed by any finite type J; reason: both descriptions give exactly the same outcome distributions, with M_j = U† P_j U
-- source:
--   Mayers, The Trouble with Quantum Bit Commitment, arXiv:quant-ph/9603015v3, section d, pp.7–8 (display on p.8)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_MayersBC_outcomeDist
import Definitions.Def_MayersBC_binaryPOVM
import Definitions.Def_MayersBC_kolmogorov
open QAlgorithms

namespace MayersBC

/-- Mayers, arXiv:quant-ph/9603015v3, section d, pp.7–8 (the display on p.8 is the proof):
"Let us show that, if the inequality K ≤ 4ε holds for any binary outcome measurement, the same
inequality holds for an arbitrary measurement." For density matrices `ρ_0, ρ_1`: if every
two-outcome measurement `{Q, I − Q}` has `K(p_0, p_1) ≤ 4ε`, then so does every measurement
`{M_j}_{j ∈ J}` with any finite outcome set `J`.

**Formalization Note.** A measurement is a POVM (`QAlgorithms.IsPOVM`): the page's operators
`M_j^{(B)} = P_j U` (an isometry followed by an orthogonal measurement, [6,14]) are exactly the
POVMs with elements `U† P_j U`. `K` has no ½. -/
theorem kolmogorov_le_of_binary {ι : Type} [Fintype ι] [DecidableEq ι] (ρ0 ρ1 : Matrix ι ι ℂ)
    (h0 : IsDensityMatrix ρ0) (h1 : IsDensityMatrix ρ1) (ε : ℝ)
    (hbin : ∀ Q : Matrix ι ι ℂ, IsEffect Q →
      kolmogorov (outcomeDist (binaryPOVM Q) ρ0) (outcomeDist (binaryPOVM Q) ρ1) ≤ 4 * ε)
    {J : Type} [Fintype J] (M : J → Matrix ι ι ℂ) (hM : IsPOVM M) :
    kolmogorov (outcomeDist M ρ0) (outcomeDist M ρ1) ≤ 4 * ε := by sorry

end MayersBC
