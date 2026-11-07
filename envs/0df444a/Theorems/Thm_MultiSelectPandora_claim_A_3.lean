-- Prove2me | Theorems.Thm_MultiSelectPandora_claim_A_3
-- name    : MultiSelectPandora.claim_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:30:26.618203+00:00
-- url     : https://prove2.me/theorems/e6a07b02-35e1-4547-b1c9-edb1ee823e56
-- title:
--   Claim A.3 — $\sigma_i$, $W$, $\mathrm{OPT}_C$, $\theta$, the grid and the laws are computable in polynomial time
-- statement:
--   Fix a rational $\varepsilon>0$ and $k\ge1$. There is a polynomial-time algorithm that, on a valid rational instance, outputs the reservation values $\sigma_i$, the quantities $W(M,0)$ and $\mathrm{OPT}_C$, and the threshold $\theta$. If $0<\mathrm{OPT}$, it also outputs the grid points $\theta_1<\dots<\theta_m$ of Definition 3.21 and the values $w_i$ and $D^L(w_i)$ by support position. If moreover $\varepsilon<1$, it outputs $I^{SL}$ as a table.
--
--   These are all rational, since each $\sigma_i$ and $\theta_l$ solves one rational linear equation on a piece of a piecewise-linear map. The statement also records p.17's "$\theta$, the grid, and $I^{SL}$ can be computed in polynomial time".
--
--   Differences from the source:
--   - reading: "polynomial in the input size, that is, in n and the total support size s", in no fixed arithmetic model → Turing.TM2ComputableInPolyTime, polynomial in the binary length of a rational input; reason: the paper fixes no model; a unit-cost model with floor is too strong to mean anything, and a cost monad would need the [FLX18a] program, which this paper does not contain
--   - encoding: Fi given explicitly, values and costs real → rational data for the machine; reason: a Turing machine reads finite words, and "given explicitly" has no other meaning for one
--   - encoding: no hypothesis on OPT → 0 < OPT; reason: θ = OPT^/ε is 0 when OPT = 0 and p.14 divides by it, so this excludes only an undefined case
--   - reading: "for fixed ε"; b_i "is well defined, since E[vi] ≤ OPT ≤ εθ < θ" (p.14) → the table is required for ε < 1 only; reason: for ε ≥ 1 the constant b_i need not be a level of I^SL, so no table exists; the other objects are required for every ε > 0
--   - reading: the grid of Definition 3.21 written with ε OPT → the grid with ε OPT^; reason: footnote 1: "the algorithm uses ε OPT^", as OPT is not known; Φ changes by at most 2ε OPT within a cell
--   - reading: ⊤ is "an arbitrary fixed number greater than MaxV" (footnote 2) → ⊤ is a number above MaxV and above every value of the instance; reason: Remark A.4 and Claim A.7 need D^L(v) ≥ v for every v; with ⊤ = MaxV + 1 Claim 3.30 fails (two boxes, value 1000 with probability 0.1, else 0, c = 90, k = 1, ε = 1/4; gap 5.23)
--   - reading: σi "the solution" of E[(vi − σi)+] = ci → the least solution; reason: the solution is not unique when ci = 0; κi is the same for every choice
--   - encoding: a law Fi with finite support → explicit support positions with values and probabilities, and expectations as finite sums with independence by product form; reason: p.5: "Each Fi is given explicitly, with finite support"
--   - encoding: "every constant k"; the searcher selects k prizes → k ≥ 1; reason: at k = 0 nothing can be selected, and the state has no floor
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Claim A.3, p.31 (PDF p.32), with p.17 (PDF p.18)

import Mathlib
import Definitions.Def_MultiSelectPandora_RawInst
import Definitions.Def_MultiSelectPandora_RawInst_Valid
import Definitions.Def_MultiSelectPandora_RawInst_toInst
import Definitions.Def_MultiSelectPandora_OPT
import Definitions.Def_MultiSelectPandora_W
import Definitions.Def_MultiSelectPandora_OPTC
import Definitions.Def_MultiSelectPandora_resv
import Definitions.Def_MultiSelectPandora_theta
import Definitions.Def_MultiSelectPandora_gridPts
import Definitions.Def_MultiSelectPandora_wVal
import Definitions.Def_MultiSelectPandora_DL
import Definitions.Def_MultiSelectPandora_IsISLtable
import Definitions.Def_MultiSelectPandora_A3Output
import Definitions.Def_MultiSelectPandora_encRawInst
import Definitions.Def_MultiSelectPandora_encA3Out

namespace MultiSelectPandora

/-- **Claim A.3 (computing the discretization)**, p.31 (PDF p.32), with p.17 (PDF p.18): "By Claim A.3, `θ`, the grid, and `I^SL` can be computed in polynomial time". Beyhaghi–Han–Luqman manuscript.

**Formalization Note.** For fixed rational `ε` and fixed `k`. "Polynomial in `n` and `s`" is `Turing.TM2ComputableInPolyTime` on binary rational instances; all the objects are rational. The grid, the laws and the table need `0 < OPT`, since `θ = 0` otherwise. The table also needs `ε < 1`: `b_i` is a small level only for `ε < 1` ("`E[v_i] ≤ OPT ≤ εθ < θ`", p.14). -/
theorem claim_A_3 (ε : ℚ) (hε : 0 < ε) (k : ℕ) (hk : 1 ≤ k) :
    ∃ f : RawInst → A3Output,
      Nonempty (Turing.TM2ComputableInPolyTime encRawInst encA3Out f) ∧
      ∀ I : RawInst, I.Valid →
        (f I).sigma.map (fun q : ℚ => (q : ℝ)) = List.ofFn (resv I.toInst) ∧
        ((f I).W : ℝ) = W I.toInst Finset.univ (0 : Fin k → ℝ) ∧
        ((f I).OPTC : ℝ) = OPTC I.toInst k ∧
        ((f I).theta : ℝ) = theta I.toInst k ε ∧
        (0 < OPT I.toInst k →
          ((f I).grid.map (fun q : ℚ => (q : ℝ))).Pairwise (· < ·) ∧
          (∀ x : ℝ, x ∈ (f I).grid.map (fun q : ℚ => (q : ℝ)) ↔ x ∈ gridPts I.toInst k ε) ∧
          (f I).wVals.map (fun l => l.map fun q : ℚ => (q : ℝ)) =
            List.ofFn (fun i => List.ofFn (wVal I.toInst k ε i)) ∧
          (f I).xVals.map (fun l => l.map fun q : ℚ => (q : ℝ)) =
            List.ofFn (fun i => List.ofFn (fun j => DL I.toInst k ε (wVal I.toInst k ε i j))) ∧
          (ε < 1 → IsISLtable ε k I (f I).table)) := by sorry

end MultiSelectPandora
