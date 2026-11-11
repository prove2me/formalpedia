-- Prove2me | Theorems.Thm_OneTrap_Core_lemma_B_7
-- name    : OneTrap.Core.lemma_B_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:47:50.773471+00:00
-- url     : https://prove2.me/theorems/ffc42891-31ee-4bc1-bdcc-900aca9cca96
-- title:
--   Lemma B.7 — at the trap level $t=\overline Z_{j^\star}$ no unknown box of higher index pays more than $t$, and some unknown box has covered wage exactly $t$
-- statement:
--   Fix $w\in W_{\mathrm{eff}}$, known boxes $K$ and unknown boxes $\mathcal U$, every unknown box having strictly positive index (after the deletion of p. 26). Suppose no known box and unknown box have the same positive finite reservation value, and fix a realized profile of the unknown outputs. If $j^\star$ is defined and $t=\overline Z_{j^\star}$, then for unknown boxes $i\in\mathcal U$
--   $$\rho_i>t\implies X_i\le t,$$
--   and some $i^\star\in\mathcal U$ has $X^{\mathrm{cov}}_{i^\star}=t$; if $t$ equals the reservation value of a known box, then $\rho_{i^\star}>t$ and $X_{i^\star}=t$. If $j^\star$ is undefined, every remaining unknown box realizes wage zero.
--
--   Differences from the source:
--   - encoding: an admissible extension A ⊇ K (finite, independent, every new box with a fresh label) → `Sum.elim K N` with `N : ν → Box` for a finite type ν (for G_K: ν = Fin n); reason: relabelling only; any number of new boxes with any admissible laws and costs, duplicates of known boxes, and A = K (ν empty) are all included
--   - encoding: ρ_i: the smallest extended-real solution of c_i = E[(X_i − ρ_i)+], with (X − ∞)+ := 0 → `resv w b` = `sInf` in EReal of the r with ∫⁻ ((w y : EReal) − r).toENNReal dF = ofReal c; reason: in EReal, X − ⊤ = ⊥ whose positive part is 0, and X − ⊥ = ⊤; the solution set is closed, so its infimum is its least element when it is nonempty (Lemma B.12)
--   - encoding: λ_j, B_j, Z_j, Z̄_j, j⋆ (pp. 26–27) → `level`, `unknownBlock`, `blockMax`, `cumBlockMax`, `jStar : Option ℕ` (none = undefined) of `Def_OneTrap_Core_Blocks`; reason: the page's construction, with the levels read off the sorted list of positive finite known indices
--   - encoding: a realized profile of the unknown boxes → any `yU : ν → ℝ` with `0 ≤ yU i`; reason: realized outputs are nonnegative (Assumption 2.1); nothing else about the profile is used
--   - reading: the standing assumption of §B.1.3 (p. 26): after the deletion every remaining unknown box has strictly positive index → hypothesis `hpos : ∀ i, 0 < ρ(N i)`; reason: the lemma is stated for the retained technology; its proof uses that every remaining unknown box has positive index
--   - reading: "some i⋆ ∈ U satisfies X^cov_{i⋆} = t. If t equals the reservation value of a known box, … ρ_{i⋆} > t and X_{i⋆} = t" → ∃ i⋆ with X^cov_{i⋆} = t and (t = ρ_k for some known k → ρ_{i⋆} > t ∧ X_{i⋆} = t); reason: the same i⋆ in both sentences
-- source:
--   Feldman, Fu, Peng, Tang (2026), One Trap Is Enough: The Structure and Complexity of Robust Contracts for Sequential Search, held STOC 2027 submission (SHA-256 8b684ffb…cf066), Lemma B.7, p. 27 (PDF 28)

import Mathlib
import Definitions.Def_OneTrap_Core_Model
import Definitions.Def_OneTrap_Core_Index
import Definitions.Def_OneTrap_Core_Blocks

open MeasureTheory

namespace OneTrap.Core

/-- Lemma B.7 (p. 27). Suppose no known box and unknown box have the same positive finite
reservation value, every unknown box has positive index (after the deletion of p. 26), and fix
a realized profile `y_U` of the unknown outputs. If `j⋆` is defined and `t = Z̄_{j⋆}`, then every
unknown box with `ρ_i > t` has `X_i ≤ t`, and some unknown `i⋆` has `X^cov_{i⋆} = t`; if `t` is the
reservation value of a known box, then `ρ_{i⋆} > t` and `X_{i⋆} = t`. If `j⋆` is undefined, every
unknown box realizes wage zero. -/
theorem lemma_B_7 {κ ν : Type*} [Fintype κ] [Fintype ν] (w : ℝ → ℝ) (hw : IsEffContract w)
    (K : κ → Box) (N : ν → Box)
    (hsep : ∀ k i, resv w (K k) = resv w (N i) → ¬ (0 < resv w (K k) ∧ resv w (K k) < ⊤))
    (hpos : ∀ i, 0 < resv w (N i)) (yU : ν → ℝ) (hyU : ∀ i, 0 ≤ yU i) :
    (∀ j : ℕ, jStar w K N yU = some j →
      (∀ i, cumBlockMax w K N yU j < resv w (N i) →
        ((w (yU i) : ℝ) : EReal) ≤ cumBlockMax w K N yU j) ∧
      ∃ istar : ν, coveredWage w (N istar) (yU istar) = cumBlockMax w K N yU j ∧
        ((∃ k, resv w (K k) = cumBlockMax w K N yU j) →
          cumBlockMax w K N yU j < resv w (N istar) ∧
          ((w (yU istar) : ℝ) : EReal) = cumBlockMax w K N yU j)) ∧
    (jStar w K N yU = none → ∀ i, w (yU i) = 0) := by sorry

end OneTrap.Core
