-- Prove2me | Theorems.Thm_IntMul_HvdH_proposition_5_4_of_clocked_step
-- name    : IntMul.HvdH.proposition_5_4_of_clocked_step
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-09T14:35:03.676595+00:00
-- url     : https://prove2.me/theorems/7231b99d-957f-4b58-a0a6-bdbe975c3745
-- title:
--   Proposition 5.4 — from clocked computations to the strict recurrence
-- statement:
--   Let $d\ge2$. Suppose a single finite multitape Turing machine $M$ multiplies correctly at every positive input length, and suppose a real constant $C$ bounds its recursive step as follows. For each admissible parameter tuple and every real budget $\tau$ permitting multiplication at length $3rp$, multiplication at length $n$ is possible within
--
--   $$\frac{12T}{r}\tau+C n\log n.$$
--
--   Then this same machine satisfies the exact strict infimum recurrence in Proposition 5.4, with overhead constant $C+1$:
--
--   $$\inf\{\tau:\operatorname{MultipliesAt}(M,n,\tau)\}<\frac{12T}{r}\inf\{\tau:\operatorname{MultipliesAt}(M,3rp,\tau)\}+(C+1)n\log n.$$
--
--   This theorem isolates the passage from a concrete clocked computation bound to the real-valued strict recurrence. The machine and its clocked step are hypotheses, not constructions supplied by this lemma.
-- source:
--   Supporting formalization of Harvey and van der Hoeven, Integer multiplication in time O(n log n), Annals of Mathematics 193(2) (2021), 563–617, DOI 10.4007/annals.2021.193.2.4; author preprint https://www.texmacs.org/joris/nlogn/nlogn.pdf, Proposition 5.4, printed pages 40–41. The clocked formulation is an explicit operational strengthening needed for the reduction, not a separately numbered theorem of the source.

import Definitions.Def_IntMul_MultitapeModel
import Definitions.Def_IntMul_HvdH_StepParameters
open IntMul IntMul.HvdH

theorem IntMul.HvdH.proposition_5_4_of_clocked_step (d : ℕ) (hd : 2 ≤ d)
    (M : MultitapeTM) (hcorrect : ∀ n : ℕ, 1 ≤ n → ∃ τ : ℝ, MultipliesAt M n τ)
    (C : ℝ)
    (hclock : ∀ n b p T r : ℕ, StepParameters d n b p T r →
      ∀ τ : ℝ, MultipliesAt M (3 * r * p) τ →
        MultipliesAt M n (12 * (T : ℝ) / r * τ + C * ((n : ℝ) * Real.log n))) :
    ∃ M : MultitapeTM, (∀ n : ℕ, 1 ≤ n → ∃ τ : ℝ, MultipliesAt M n τ) ∧
      ∃ C : ℝ, ∀ n : ℕ, 2 ^ (d ^ 12) ≤ n →
        ∀ b p T r : ℕ, b = Nat.clog 2 n → p = 6 * b →
          (∃ k : ℕ, T = 2 ^ k) → 4 * (n : ℝ) / b ≤ T → (T : ℝ) < 8 * (n : ℝ) / b →
          (∃ j : ℕ, r = 2 ^ j) → (T : ℝ) ^ ((1 : ℝ) / d) ≤ r →
          (r : ℝ) < 2 * (T : ℝ) ^ ((1 : ℝ) / d) →
          sInf {τ : ℝ | MultipliesAt M n τ} <
            12 * (T : ℝ) / r * sInf {τ : ℝ | MultipliesAt M (3 * r * p) τ} +
              C * ((n : ℝ) * Real.log n) := by sorry
