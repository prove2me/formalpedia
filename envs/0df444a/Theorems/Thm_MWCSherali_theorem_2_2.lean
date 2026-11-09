-- Prove2me | Theorems.Thm_MWCSherali_theorem_2_2
-- name    : MWCSherali.theorem_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:16:14.957931+00:00
-- url     : https://prove2.me/theorems/7cfa2292-039e-4202-ac09-4aea9309894f
-- title:
--   Theorem 2.2 ([AMM17]) — non-opposite cut gaps give UG-hardness
-- statement:
--   Let $n\ge1$ and let $w:E_{k,n}\to\mathbb R_{\ge0}$ be normalized, $\sum_{e}w_e=n$. Assuming the Unique Games Conjecture, for every $\epsilon>0$ there is $K$ such that for every number of terminals $k'\ge K$ it is NP-hard to approximate Multiway Cut on $k'$-terminal instances within a multiplicative factor of
--
--   $$\mathrm{OPT}^{\mathrm{no}}(w)-\epsilon .$$
--
--   This result of Angelidakis, Makarychev and Manurangsi, combined with the translation of integrality gaps into UG-hardness by Manokaran, Naor, Raghavendra and Schwartz, is cited by the paper and not proved there. It turns a gap on a small simplex into hardness for Multiway Cut with many terminals.
--
--   Differences from the source:
--   - encoding: n a positive integer (p.4) → hypothesis 0 < n; reason: Δ_{k,n} is defined only for positive n
--   - encoding: points x ∈ Δ_{k,n} with coordinates in (1/n)ℤ, 1-based indices → integer coordinates y = n x (Grid k n), 0-based indices; reason: Lean convention; the same points
--   - encoding: w : E_{k,n} → ℝ_{≥0} → w : Sym2 (Grid k n) → ℝ, nonnegative on E_{k,n}; reason: only the values on E_{k,n} are ever used
--   - encoding: labels [k+1] with neutral label k+1 → labels Fin (k+1), terminal i as i − 1, neutral label as Fin.last k; reason: Lean convention; same labelings
--   - encoding: the Unique Games Conjecture [Kho02] (not stated in the paper) → OptInapprox.MaxCut.UGC: for all η, γ > 0 there is M such that Unique Label Cover with M labels is gap NP-hard for (1 − η, γ); reason: the standard statement of the conjecture, from a published module
--   - reading: "NP-hard to approximate within a factor of ρ" → gap NP-hardness: for some c > 0 and s > ρc, distinguishing instances with a multiway cut of weight ≤ cW from instances whose multiway cuts all weigh ≥ sW is NP-hard (W > 0, at least one terminal); reason: the standard meaning; a ρ-approximation algorithm decides this gap problem
--   - reading: weighted graphs with w : E → ℝ_+ → natural-number weights written as edge multiplicities (unary multigraph encoding); reason: hardness on this subclass implies hardness for rational or real weights under any reasonable encoding
--   - reading: "with sufficiently many terminals" → ∃ K, ∀ k' ≥ K, hardness on instances with exactly k' terminals; reason: the stronger of the two readings (the other is "for some k'"); adding isolated terminals makes them equivalent
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), Theorem 2.2 ([AMM17]), p.14

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_UGC
import Definitions.Def_MWCSherali_Grid
import Definitions.Def_MWCSherali_edges
import Definitions.Def_MWCSherali_IsNormalized
import Definitions.Def_MWCSherali_OPTno
import Definitions.Def_MWCSherali_MWCHardOn

namespace MWCSherali

open OptInapprox.MaxCut

/-- **Theorem 2.2 ([AMM17]: non-opposite cut gaps give UG-hardness).** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3, 2026),
Theorem 2.2, p.14: "Let `w : E_{k,n} → ℝ_{≥0}` be normalized. Assuming the Unique Games
Conjecture, for every `ϵ > 0`, it is NP-hard to approximate Multiway Cut, with sufficiently many
terminals, within a multiplicative factor of `OPT^no(w) − ϵ`."

The paper cites this result from Angelidakis–Makarychev–Manurangsi (with the hardness
translation of Manokaran–Naor–Raghavendra–Schwartz); it does not prove it.

**Formalization Note.**
* "With sufficiently many terminals" is read as: there is `K` such that for every number of
  terminals `k' ≥ K` the problem restricted to `k'`-terminal instances is hard
  (`MWCHardOn (· = k')`). This is the stronger of the two readings ("for some `k'`" is the
  other); adding isolated terminals makes them equivalent.
* `UGC` is the Unique Games Conjecture of the reused module `OptInapprox.MaxCut`.
* The paper's `n` is a positive integer. -/
theorem theorem_2_2 (k n : ℕ) (hn : 0 < n) (w : Sym2 (Grid k n) → ℝ)
    (hw : ∀ e ∈ edges k n, 0 ≤ w e) (hnorm : IsNormalized w) :
    UGC → ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k' ≥ K, MWCHardOn (· = k') (OPTno w - ε) := by sorry

end MWCSherali
