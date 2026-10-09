-- Prove2me | Theorems.Thm_OAI_Erdos3_adaptiveAffineSideLog_reference_bound
-- name    : OAI.Erdos3.adaptiveAffineSideLog_reference_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T17:45:18.458905+00:00
-- url     : https://prove2.me/theorems/f7d50258-79a4-4e77-914b-f33b62456871
-- title:
--   The adaptive affine side logarithm at the reference degree is at most a quartic budget
-- statement:
--   Let $E$, $\mathrm{sourceDim}$, $\mathrm{siteDim}$ be natural numbers and $\varepsilon, L, T, C, \mathrm{totalShell}, \mathrm{modLog}, \mathrm{dimLog}, U$ real numbers, with $2 \le E$, $0 < \varepsilon \le 1$, $0 \le U$, $0 \le L$, $0 \le T$, $0 \le C$, $0 \le \mathrm{modLog}$, $L \le U$, $T \le U$, $C \le U$, $\mathrm{modLog} \le U$, $\mathrm{dimLog} \le U$, $\mathrm{sourceDim} \le U$, $\mathrm{siteDim} \le U$, $\varepsilon^{-1} \le e^{U}$, $0 < \mathrm{totalShell}$ and $\mathrm{totalShell}^{-1} \le e^{U}$. Let $A = \lceil (\texttt{affineReferenceInput}\ \varepsilon\ U + 2)^E \rceil$ (natural-number ceiling), where `affineReferenceInput ε U` is an explicit real-valued function of OpenAI. Then
--   $$\texttt{adaptiveAffineSideLog}\ A\ \mathrm{sourceDim}\ \mathrm{siteDim}\ \varepsilon\ L\ T\ C\ \mathrm{totalShell}\ \mathrm{modLog}\ \mathrm{dimLog} \le 65536\,\bigl(\texttt{affineCommonReferenceBudget}\ E\ \varepsilon\ U + 3\bigr)^4,$$
--   where `adaptiveAffineSideLog` is OpenAI's real-valued quantity $\mathrm{modLog} \cdot A + {}$`affineComparisonLengthLog` (evaluated at the natural number `adaptiveAffineCutoff A sourceDim siteDim ε L T C totalShell modLog`) $+ 2$, and `affineCommonReferenceBudget E ε U` $= 2\,(\texttt{affineReferenceInput}\ \varepsilon\ U + 2)^E$.
--
--   Lean: `OAI.Erdos3.adaptiveAffineSideLog_reference_bound` in `lean/OAI/Combinatorics/Progressions/Lattices/AffineCommonReferenceBudget.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B090` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AffineCommonReferenceBudget.lean#L101

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem adaptiveAffineSideLog_reference_bound {E sourceDim siteDim : ℕ}
    {epsilon L T C totalShell modLog dimLog U : ℝ}
    (hE : 2 ≤ E) (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hU : 0 ≤ U)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C) (hmod0 : 0 ≤ modLog)
    (hLU : L ≤ U) (hTU : T ≤ U) (hCU : C ≤ U) (hmod : modLog ≤ U) (hdim : dimLog ≤ U)
    (hsource : (sourceDim : ℝ) ≤ U) (hsite : (siteDim : ℝ) ≤ U)
    (hinverse : epsilon⁻¹ ≤ Real.exp U) (htotal : 0 < totalShell) (htotalInv : totalShell⁻¹ ≤ Real.exp U) :
    adaptiveAffineSideLog ⌈(affineReferenceInput epsilon U + 2) ^ E⌉₊ sourceDim siteDim
      epsilon L T C totalShell modLog dimLog ≤ 65536 * (affineCommonReferenceBudget E epsilon U + 3) ^ 4 := by
  sorry

end Erdos3
end
end OAI
