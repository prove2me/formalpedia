-- Prove2me | Theorems.Thm_IntMul_HvdH_clocked_recursive_multiplier
-- name    : IntMul.HvdH.clocked_recursive_multiplier
-- status  : Open
-- author  : @abcdefg
-- created : 2026-10-09T14:34:46.164164+00:00
-- url     : https://prove2.me/theorems/c92140cc-be98-41c7-98f0-a01968ec5e42
-- title:
--   Proposition 5.4 — correct recursive machine with a clocked cost bound
-- statement:
--   For every natural number $d\ge2$, construct one finite multitape Turing machine $M$ that multiplies correctly at every positive input length, together with a real constant $C$. For every tuple satisfying the parameter constraints of Proposition 5.4 and every real budget $\tau$, require
--
--   $$\operatorname{MultipliesAt}(M,3rp,\tau)\Longrightarrow\operatorname{MultipliesAt}\left(M,n,\frac{12T}{r}\tau+C n\log n\right).$$
--
--   The machine may depend on $d$; its alphabet, state set and transition function must be finite. The constant is independent of $n,b,p,T,r,\tau$. Both correctness and this cost guarantee concern the same machine and its actual transition-step semantics.
--
--   This is the open implementation obligation in the decomposition of Proposition 5.4. It expresses the paper's recursive algorithm as a stronger operational budget-transfer statement. It does not assume Proposition 5.4 or Theorem 1.1.
-- source:
--   Supporting formalization of Harvey and van der Hoeven, Integer multiplication in time O(n log n), Annals of Mathematics 193(2) (2021), 563–617, DOI 10.4007/annals.2021.193.2.4; author preprint https://www.texmacs.org/joris/nlogn/nlogn.pdf, Proposition 5.4, printed pages 40–41. The clocked formulation is an explicit operational strengthening needed for the reduction, not a separately numbered theorem of the source.

import Definitions.Def_IntMul_MultitapeModel
import Definitions.Def_IntMul_HvdH_StepParameters

theorem IntMul.HvdH.clocked_recursive_multiplier (d : ℕ) (hd : 2 ≤ d) :
    ∃ M : IntMul.MultitapeTM,
      (∀ n : ℕ, 1 ≤ n → ∃ τ : ℝ, IntMul.MultipliesAt M n τ) ∧
      ∃ C : ℝ, ∀ n b p T r : ℕ, IntMul.HvdH.StepParameters d n b p T r →
        ∀ τ : ℝ, IntMul.MultipliesAt M (3 * r * p) τ →
          IntMul.MultipliesAt M n
            (12 * (T : ℝ) / r * τ + C * ((n : ℝ) * Real.log n)) := by sorry
