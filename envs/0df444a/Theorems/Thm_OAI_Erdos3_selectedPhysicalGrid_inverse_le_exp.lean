-- Prove2me | Theorems.Thm_OAI_Erdos3_selectedPhysicalGrid_inverse_le_exp
-- name    : OAI.Erdos3.selectedPhysicalGrid_inverse_le_exp
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T17:31:26.979719+00:00
-- url     : https://prove2.me/theorems/3a3b6e3b-c228-49ef-8bb6-7f977248480e
-- title:
--   The inverse selected physical grid accuracy is at most an explicit exponential
-- statement:
--   Let $J$ be a finite type with decidable equality, $m, n \in \mathbb{N}$, $k \in J$, $D \in \mathbb{N}$, and $K, A, C, C_w, c, \varepsilon, P$ real numbers with $0 \le P$, $0 \le K$, $0 \le A$, $0 \le C$, $0 \le C_w$, $0 < c$, $0 < \varepsilon$, $0 < D$, and each of $n$, $|J|$, $D$, $K$, $A$, $C$, $C_w$, $c^{-1}$, $\varepsilon^{-1}$ and `probabilityProfileLipschitz` (an $\mathbb{R}_{\ge 0}$-valued constant chosen by OpenAI) at most $e^{P}$. Put $\tau = $ `weightedReplacementTolerance ((3K)^m) (2^(n+1) A^n) ε` (with `weightedReplacementTolerance F E ε` $= \min(1, \varepsilon^2/(1 + F^2(1+E)))$), $\kappa = $ `integerBoxRetainedGap |J| D c τ` $= D \cdot \min\bigl(1, \tau/(1 + 2 \cdot 3^{|J|})\bigr) \cdot c$, and $Z = $ `replacementCommonInputLog m n |J| P` (an explicit real-valued function of OpenAI). (The statement also introduces $D \cdot$ `integerBoxGcdCutoff |J| C_w τ`, which does not enter the conclusion.) Then
--   $$\bigl(\texttt{physicalPairGridAccuracy}\ n\ k\ C\ \kappa\ A\ \tau\bigr)^{-1} \le \exp\bigl(2 \cdot \texttt{physicalPairCoefficientLog}\ n\ d'\ Z + 2\bigr),$$
--   where $d'$ is the number of $j \in J$ with $j \neq k$, and `physicalPairGridAccuracy` and `physicalPairCoefficientLog` are explicit real-valued functions of OpenAI.
--
--   Lean: `OAI.Erdos3.selectedPhysicalGrid_inverse_le_exp` in `lean/OAI/Combinatorics/Progressions/Sampling/SelectedPhysicalGridBudget.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B090` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/SelectedPhysicalGridBudget.lean#L9

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

namespace OAI

section

namespace Erdos3

theorem selectedPhysicalGrid_inverse_le_exp {J : Type*} [Fintype J] [DecidableEq J]
    (m n : ℕ) (k : J) (D : ℕ) {K A C Cwidth c epsilon P : ℝ}
    (hP : 0 ≤ P) (hK0 : 0 ≤ K) (hA0 : 0 ≤ A) (hC0 : 0 ≤ C) (hCwidth0 : 0 ≤ Cwidth)
    (hc0 : 0 < c) (heps0 : 0 < epsilon) (hD : 0 < D)
    (hn : (n : ℝ) ≤ Real.exp P) (hcard : (Fintype.card J : ℝ) ≤ Real.exp P)
    (hDlog : (D : ℝ) ≤ Real.exp P) (hK : K ≤ Real.exp P) (hA : A ≤ Real.exp P)
    (hC : C ≤ Real.exp P) (hCwidth : Cwidth ≤ Real.exp P)
    (hc : c⁻¹ ≤ Real.exp P) (heps : epsilon⁻¹ ≤ Real.exp P)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) :
    let tol := weightedReplacementTolerance ((3 * K) ^ m) ((2 : ℝ) ^ (n + 1) * A ^ n) epsilon
    let _Q := D * integerBoxGcdCutoff (Fintype.card J) Cwidth tol
    let κ := integerBoxRetainedGap (Fintype.card J) D c tol
    let Z := replacementCommonInputLog m n (Fintype.card J) P
    (physicalPairGridAccuracy n k C κ A tol)⁻¹ ≤
      Real.exp (2 * physicalPairCoefficientLog n (Fintype.card {j : J // j ≠ k}) Z + 2) := by
  sorry

end Erdos3
end
end OAI
