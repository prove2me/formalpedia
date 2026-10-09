-- Prove2me | Theorems.Thm_OAI_Erdos3_selectedPhysicalReplacementThreshold_le_exp
-- name    : OAI.Erdos3.selectedPhysicalReplacementThreshold_le_exp
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T17:32:52.607318+00:00
-- url     : https://prove2.me/theorems/89b5da3b-fca6-4cf8-b112-7ed380dd0794
-- title:
--   The selected physical replacement scale threshold is at most an explicit exponential
-- statement:
--   Let $J$ be a finite type with decidable equality, let $m, n, \mathrm{degree}, D$ be natural numbers with $0 < D$, let $k \in J$, and let $K, A, C, C_{\mathrm{width}}, c, \varepsilon, P$ be real numbers. Assume $0 \le P$, $0 \le K$, $0 \le A$, $0 \le C$, $0 \le C_{\mathrm{width}}$, $0 < c$, $0 < \varepsilon$, and that each of $n$, $|J|$, $D$, $K$, $A$, $C$, $C_{\mathrm{width}}$, $c^{-1}$, $\varepsilon^{-1}$ and the constant `probabilityProfileLipschitz` (a nonnegative real constant chosen by OpenAI) is at most $e^{P}$. Put
--   $\mathrm{tol} = $ `weightedReplacementTolerance` $\bigl((3K)^m,\ 2^{n+1}A^n,\ \varepsilon\bigr)$, where `weightedReplacementTolerance F E ε` $= \min\bigl(1, \varepsilon^2/(1 + F^2(1+E))\bigr)$;
--   $Q = D \cdot$ `integerBoxGcdCutoff` $(|J|, C_{\mathrm{width}}, \mathrm{tol})$, a natural number;
--   $\kappa = $ `integerBoxRetainedGap` $(|J|, D, c, \mathrm{tol})$, a real number;
--   and $Z = $ `replacementCommonInputLog` $(m, n, |J|, P)$, a real number. Then
--   $$\texttt{physicalReplacementScaleThreshold}\ n\ k\ Q\ C\ \kappa\ A\ \mathrm{tol}\ \mathrm{degree}\ Z\ Z \le \exp\bigl(2\cdot\texttt{physicalReplacementThresholdLog}\ n\ |J\setminus\{k\}|\ \mathrm{degree}\ Z + 16\bigr),$$
--   where `physicalReplacementScaleThreshold` and `physicalReplacementThresholdLog` are real-valued functions defined by OpenAI, and $|J\setminus\{k\}|$ is the cardinality of the subtype $\{j : J \mid j \ne k\}$.
--
--   Lean: `OAI.Erdos3.selectedPhysicalReplacementThreshold_le_exp` in `lean/OAI/Combinatorics/Progressions/Dynamics/InitialBudgetJointReplacement.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B090` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Dynamics/InitialBudgetJointReplacement.lean#L148

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

theorem selectedPhysicalReplacementThreshold_le_exp {J : Type*} [Fintype J] [DecidableEq J]
    (m n degree : ℕ) (k : J) (D : ℕ) {K A C Cwidth c epsilon P : ℝ}
    (hP : 0 ≤ P) (hK0 : 0 ≤ K) (hA0 : 0 ≤ A) (hC0 : 0 ≤ C) (hCwidth0 : 0 ≤ Cwidth)
    (hc0 : 0 < c) (heps0 : 0 < epsilon) (hD : 0 < D)
    (hn : (n : ℝ) ≤ Real.exp P) (hcard : (Fintype.card J : ℝ) ≤ Real.exp P)
    (hDlog : (D : ℝ) ≤ Real.exp P) (hK : K ≤ Real.exp P) (hA : A ≤ Real.exp P)
    (hC : C ≤ Real.exp P) (hCwidth : Cwidth ≤ Real.exp P)
    (hc : c⁻¹ ≤ Real.exp P) (heps : epsilon⁻¹ ≤ Real.exp P)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) :
    let tol := weightedReplacementTolerance ((3 * K) ^ m) ((2 : ℝ) ^ (n + 1) * A ^ n) epsilon
    let Q := D * integerBoxGcdCutoff (Fintype.card J) Cwidth tol
    let κ := integerBoxRetainedGap (Fintype.card J) D c tol
    let Z := replacementCommonInputLog m n (Fintype.card J) P
    physicalReplacementScaleThreshold n k Q C κ A tol degree Z Z ≤
      Real.exp (2 * physicalReplacementThresholdLog n (Fintype.card {j : J // j ≠ k}) degree Z + 16) := by
  sorry

end Erdos3
end
end OAI
