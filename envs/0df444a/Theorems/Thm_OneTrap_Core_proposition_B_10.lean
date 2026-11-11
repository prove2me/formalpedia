-- Prove2me | Theorems.Thm_OneTrap_Core_proposition_B_10
-- name    : OneTrap.Core.proposition_B_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:46:47.289599+00:00
-- url     : https://prove2.me/theorems/859ac44a-603c-414e-a98e-c35461a128f4
-- title:
--   Proposition B.10 — one-trap approximation when no positive finite unknown index equals a positive finite known index
-- statement:
--   Fix $w\in W_{\mathrm{eff}}$ and a finite extension $A\supseteq K$. Suppose no positive finite unknown index equals a positive finite known index. For every $\varepsilon>0$ there is $\tilde A=K$ or $\tilde A=K\cup\{\mathrm{trap}(y,t)\}$ such that
--   $$V_P(w\mid\tilde A)\le V_P(w\mid A)+\varepsilon;$$
--   in the second case $0<t\le w(y)$.
--
--   Differences from the source:
--   - generalization: A is the retained extension of §B.1.3 (p. 26), whose unknown boxes all have strictly positive index → no assumption on the sign of the unknown indices; reason: deleting unknown boxes of index ≤ 0 does not raise V_P(w | A) (§B.1.3 display), so this follows from the source's statement and specializes to it
--   - encoding: an admissible extension A ⊇ K (finite, independent, every new box with a fresh label) → `Sum.elim K N` with `N : ν → Box` for a finite type ν (for G_K: ν = Fin n); reason: relabelling only; any number of new boxes with any admissible laws and costs, duplicates of known boxes, and A = K (ν empty) are all included
--   - encoding: K ∪ {trap(y, t)}, trap(y, t) a fresh box returning y with probability one at cost w(y) − t (Definition 3.1) → `withTrap w K y t hy ht` = `Sum.elim K (fun _ : Unit => trap w y t hy ht)` on `κ ⊕ Unit`, the trap having law δ_y and cost w y − t; reason: one fresh box; the side conditions y ≥ 0 and t ≤ w(y) are carried by the proofs hy, ht
--   - encoding: V_P(w | Ã) ≤ V_P(w | A) + ε → the same inequality in EReal with ε coerced from ℝ; reason: values are extended reals; for w ∈ W_eff they are real (Proposition 2.3)
--   - encoding: V_P(w | A) = max of P_A(w, π) over Σ⋆(w, A) = argmax U_A(w, ·) (Definition 2.2) → `VP w T` = `sSup` in EReal of `principalValue` over `agentOptimal` (⊥ if that set were empty); the null output is the initial outcome with pair (w 0, 0 − w 0); reason: both maxima are attained (Fact A.1), and an attained supremum is the maximum
-- source:
--   Feldman, Fu, Peng, Tang (2026), One Trap Is Enough: The Structure and Complexity of Robust Contracts for Sequential Search, held STOC 2027 submission (SHA-256 8b684ffb…cf066), Proposition B.10, p. 30 (PDF 31)

import Mathlib
import Definitions.Def_OneTrap_Core_Model
import Definitions.Def_OneTrap_Core_Search
import Definitions.Def_OneTrap_Core_Index

open MeasureTheory

namespace OneTrap.Core

/-- Proposition B.10 (p. 30). Suppose no positive finite unknown index equals a positive finite
known index. For every `ε > 0` there is `Ã = K` or `Ã = K ∪ {trap(y, t)}` with
`V_P(w | Ã) ≤ V_P(w | A) + ε`; in the second case `0 < t ≤ w(y)`. -/
theorem proposition_B_10 {κ ν : Type*} [Fintype κ] [DecidableEq κ] [Fintype ν] [DecidableEq ν]
    (w : ℝ → ℝ) (hw : IsEffContract w) (K : κ → Box) (N : ν → Box)
    (hsep : ∀ (k : κ) (i : ν), 0 < resv w (N i) → resv w (N i) < ⊤ →
      0 < resv w (K k) → resv w (K k) < ⊤ → resv w (N i) ≠ resv w (K k))
    (ε : ℝ) (hε : 0 < ε) :
    VP w K ≤ VP w (Sum.elim K N) + ((ε : ℝ) : EReal) ∨
    ∃ (y t : ℝ) (hy : 0 ≤ y) (ht : t ≤ w y), 0 < t ∧
      VP w (withTrap w K y t hy ht) ≤ VP w (Sum.elim K N) + ((ε : ℝ) : EReal) := by sorry

end OneTrap.Core
