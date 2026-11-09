-- Prove2me | Theorems.Thm_MWCSherali_lemma_2_5
-- name    : MWCSherali.lemma_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:17:21.769585+00:00
-- url     : https://prove2.me/theorems/4e4294f3-c154-48ba-87c1-54a13572b0c7
-- title:
--   Lemma 2.5 — feasible dual solutions certify UG-hardness
-- statement:
--   Let $n\ge1$ and let $(y_C)_C$, $(z_{C,x,a})_{C,x,a}$, $(w_e)_e$ be a feasible solution of (dual-LP$^{\mathrm{no}}_{\mathrm{vertex}}$-w) with
--
--   $$\sum_{C\in D_{k,n}}y_C=r>0 .$$
--
--   Then, assuming the Unique Games Conjecture, Multiway Cut is NP-hard to approximate within a factor of $r-\epsilon$, for any $\epsilon>0$.
--
--   The lemma reduces UG-hardness to exhibiting one feasible dual solution; Theorem 3.2 produces such solutions from flows.
--
--   Differences from the source:
--   - encoding: n a positive integer (p.4) → hypothesis 0 < n; reason: Δ_{k,n} is defined only for positive n
--   - encoding: points x ∈ Δ_{k,n} with coordinates in (1/n)ℤ, 1-based indices → integer coordinates y = n x (Grid k n), 0-based indices; reason: Lean convention; the same points
--   - encoding: labels [k+1] with neutral label k+1 → labels Fin (k+1), terminal i as i − 1, neutral label as Fin.last k; reason: Lean convention; same labelings
--   - encoding: cells C ∈ D_{k,n} → cells indexed by V ∈ Δ_{k,n+1} (Grid k (n+1)); reason: the paper's one-to-one correspondence D_{k,n} ↔ Δ_{k,n+1} (p.15)
--   - encoding: the Unique Games Conjecture [Kho02] (not stated in the paper) → OptInapprox.MaxCut.UGC: for all η, γ > 0 there is M such that Unique Label Cover with M labels is gap NP-hard for (1 − η, γ); reason: the standard statement of the conjecture, from a published module
--   - reading: "NP-hard to approximate within a factor of ρ" → gap NP-hardness: for some c > 0 and s > ρc, distinguishing instances with a multiway cut of weight ≤ cW from instances whose multiway cuts all weigh ≥ sW is NP-hard (W > 0, at least one terminal); reason: the standard meaning; a ρ-approximation algorithm decides this gap problem
--   - reading: weighted graphs with w : E → ℝ_+ → natural-number weights written as edge multiplicities (unary multigraph encoding); reason: hardness on this subclass implies hardness for rational or real weights under any reasonable encoding
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), Lemma 2.5, p.17

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_UGC
import Definitions.Def_MWCSherali_Grid
import Definitions.Def_MWCSherali_DualVertexWFeasible
import Definitions.Def_MWCSherali_MWCHard

namespace MWCSherali

open OptInapprox.MaxCut

/-- **Lemma 2.5 (dual solutions certify UG-hardness).** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3, 2026), Lemma 2.5, p.17:
"Let `(y_C)_C, (z_{C,x,a})_{C,x,a}, (w_e)_e` be a feasible solution to (dual-LP^no_vertex-w) for some
`k, n ∈ ℕ`, with `∑_C y_C = r > 0`. Then assuming the Unique Games Conjecture, Multiway Cut is
NP-hard to approximate within a factor of `r − ϵ`, for any `ϵ > 0`."

**Formalization Note.** Hardness is `MWCHard` (gap NP-hardness, ratio strictly above `r − ϵ`, the
number of terminals part of the input). Cells are indexed by `V : Grid k (n+1)`. The paper's `n`
is a positive integer. -/
theorem lemma_2_5 (k n : ℕ) (hn : 0 < n) (y : Grid k (n + 1) → ℝ)
    (z : Grid k (n + 1) → Grid k n → Fin (k + 1) → ℝ) (w : Sym2 (Grid k n) → ℝ)
    (hfeas : DualVertexWFeasible k n y z w) (r : ℝ) (hr : ∑ V, y V = r) (hr0 : 0 < r) :
    UGC → ∀ ε : ℝ, 0 < ε → MWCHard (r - ε) := by sorry

end MWCSherali
