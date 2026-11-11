-- Prove2me | Theorems.Thm_OneTrap_Core_deletion_B_1_3
-- name    : OneTrap.Core.deletion_B_1_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:46:33.533437+00:00
-- url     : https://prove2.me/theorems/3d02478e-9140-44f2-b8e1-17a3be79f3c1
-- title:
--   §B.1.3 deletion display — deleting an unknown box of index $\rho_i\le 0$ does not raise $V_P$
-- statement:
--   Fix $w\in W_{\mathrm{eff}}$ and a finite extension $A\supseteq K$. If an unknown box $i\in A\setminus K$ has $\rho_i\le 0$, then
--   $$V_P(w\mid A\setminus\{i\})\le V_P(w\mid A).$$
--
--   Differences from the source:
--   - encoding: an admissible extension A ⊇ K (finite, independent, every new box with a fresh label) → `Sum.elim K N` with `N : ν → Box` for a finite type ν (for G_K: ν = Fin n); reason: relabelling only; any number of new boxes with any admissible laws and costs, duplicates of known boxes, and A = K (ν empty) are all included
--   - encoding: ρ_i: the smallest extended-real solution of c_i = E[(X_i − ρ_i)+], with (X − ∞)+ := 0 → `resv w b` = `sInf` in EReal of the r with ∫⁻ ((w y : EReal) − r).toENNReal dF = ofReal c; reason: in EReal, X − ⊤ = ⊥ whose positive part is 0, and X − ⊥ = ⊤; the solution set is closed, so its infimum is its least element when it is nonempty (Lemma B.12)
--   - encoding: V_P(w | A) = max of P_A(w, π) over Σ⋆(w, A) = argmax U_A(w, ·) (Definition 2.2) → `VP w T` = `sSup` in EReal of `principalValue` over `agentOptimal` (⊥ if that set were empty); the null output is the initial outcome with pair (w 0, 0 − w 0); reason: both maxima are attained (Fact A.1), and an attained supremum is the maximum
--   - encoding: A \ {i} → `Sum.elim K (fun j : {j : ν // j ≠ i} => N j)`; reason: the extension without the unknown box i
-- source:
--   Feldman, Fu, Peng, Tang (2026), One Trap Is Enough: The Structure and Complexity of Robust Contracts for Sequential Search, held STOC 2027 submission (SHA-256 8b684ffb…cf066), §B.1.3, display on p. 26 (PDF 27)

import Mathlib
import Definitions.Def_OneTrap_Core_Model
import Definitions.Def_OneTrap_Core_Search
import Definitions.Def_OneTrap_Core_Index

open MeasureTheory

namespace OneTrap.Core

/-- §B.1.3, display on p. 26. Deleting from a finite extension `A ⊇ K` an unknown box `i` with
`ρ_i ≤ 0` does not raise the principal-favored value: `V_P(w | A \ {i}) ≤ V_P(w | A)`. -/
theorem deletion_B_1_3 {κ ν : Type*} [Fintype κ] [DecidableEq κ] [Fintype ν] [DecidableEq ν]
    (w : ℝ → ℝ) (hw : IsEffContract w) (K : κ → Box) (N : ν → Box) (i : ν)
    (hi : resv w (N i) ≤ 0) :
    VP w (Sum.elim K fun j : {j : ν // j ≠ i} => N j) ≤ VP w (Sum.elim K N) := by sorry

end OneTrap.Core
