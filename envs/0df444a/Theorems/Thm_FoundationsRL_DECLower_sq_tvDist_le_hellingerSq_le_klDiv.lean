-- Prove2me | Theorems.Thm_FoundationsRL_DECLower_sq_tvDist_le_hellingerSq_le_klDiv
-- name    : FoundationsRL.DECLower.sq_tvDist_le_hellingerSq_le_klDiv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:18:28.678595+00:00
-- url     : https://prove2.me/theorems/c8aea163-af2b-46d4-bae5-64d9e933c3f0
-- title:
--   Lemma 19 — $D^2_{\mathrm{TV}}\le D^2_{\mathrm H}\le D_{\mathrm{KL}}$
-- statement:
--   Let $P$ and $Q$ be probability measures on a measurable space $(\Omega,\mathcal F)$. Then
--
--   $$
--   D^2_{\mathrm{TV}}(P,Q)\le D^2_{\mathrm H}(P,Q)\le D_{\mathrm{KL}}(P\,\|\,Q).
--   $$
--
--   Both inequalities are part of the statement. The chain converts closeness in KL divergence, which the chain rule makes computable for interaction histories, into closeness in total variation and Hellinger distance, which control expectations of bounded functions.
--
--   **Formalization Note** The squared Hellinger distance has no factor $1/2$, and KL divergence is Mathlib's; both are in $[0,\infty]$, and the real square of $D_{\mathrm{TV}}$ is embedded there.
--
--   Differences from the source:
--   - encoding: $D^2_{\mathrm{TV}}$ a real number compared with $D^2_{\mathrm H}$ and $D_{\mathrm{KL}}$ → the real square embedded in $[0,\infty]$, with $D^2_{\mathrm H}$ and $D_{\mathrm{KL}}$ valued in $[0,\infty]$; reason: Lean convention, $D_{\mathrm{KL}}$ can be $+\infty$; same instances
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Lemma 19, (6.6), p. 96

import Mathlib
import Definitions.Def_FoundationsRL_DECLower_tvDist
import Definitions.Def_FoundationsRL_DECLower_hellingerSq

open MeasureTheory InformationTheory
open scoped ENNReal

namespace FoundationsRL.DECLower

/-- **Lemma 19, (6.6): `D²_TV(P, Q) ≤ D²_H(P, Q) ≤ D_KL(P ∥ Q)`.**
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, Lemma 19, (6.6), p. 96: "For all distributions P and Q,
D²_TV(P, Q) ≤ D²_H(P, Q) ≤ D_KL(P ∥ Q)."

For probability measures `μ, ν` on any measurable space, both inequalities hold.

**Formalization Note.** `D_TV` is real-valued (in `[0, 1]`), so its square is embedded in `ℝ≥0∞`
with `ENNReal.ofReal`; `D²_H` (no factor `1/2`) and Mathlib's `klDiv` are in `ℝ≥0∞`. -/
theorem sq_tvDist_le_hellingerSq_le_klDiv {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ENNReal.ofReal (tvDist μ ν ^ 2) ≤ hellingerSq μ ν ∧ hellingerSq μ ν ≤ klDiv μ ν := by sorry

end FoundationsRL.DECLower
