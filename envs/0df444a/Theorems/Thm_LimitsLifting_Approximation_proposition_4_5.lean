-- Prove2me | Theorems.Thm_LimitsLifting_Approximation_proposition_4_5
-- name    : LimitsLifting.Approximation.proposition_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:39:24.486101+00:00
-- url     : https://prove2.me/theorems/4095286d-256d-4b02-9c7d-eed1ea2eed68
-- title:
--   Proposition 4.5 — $\mu(f,\mathcal M)$ lower-bounds $\mathrm{Size}^+(f)$, and $\mathrm{Size}(f)$ for non-monotone models
-- statement:
--   Let $f$ be a partial monotone Boolean function with domain $Z\subseteq\{0,1\}^\iota$ ($\iota$ finite) and let $\langle\mathcal M,\bar\vee,\bar\wedge\rangle$ be an approximation model over $Z$. Then
--   $$\mu(f,\mathcal M)\le\mathrm{Size}^+(f),$$
--   and if the model is non-monotone (it contains every negated input $\neg x_i$), then
--   $$\mu(f,\mathcal M)\le\mathrm{Size}(f).$$
--
--   This is the approximation method in its quantitative form: replacing each gate of a circuit for $f$ by its approximating gate costs at most $\delta$ per gate, while every member of the model errs with probability at least $\varepsilon$.
--
--   Differences from the source:
--   - generalization: the bound μ ≤ Size⁺(f) for monotone models → for every approximation model; reason: a monotone circuit uses only inputs and constants, which every model contains; monotone models are a special case.
--   - encoding: inputs indexed by [n] → by an arbitrary finite type; reason: same instances up to renaming.
--   - generalization: positive input arity and the balanced probability law on two nonempty label classes → empty input type and empty or one-label domains are also allowed, with a zero contribution from an empty class; reason: in these extra cases f is constant or has empty domain, so f belongs to every model and ε = μ = 0; both inequalities still hold.
-- source:
--   Gaia Carenini, Bruno Cavalar, Stefan Grosser, Jan Pich, Limits of Lifting, STOC 2027 submission #309 (October 2026), Proposition 4.5, printed p. 19 (PDF p. 20)

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF
import Definitions.Def_LimitsLifting_Approximation_ApproxModel
import Definitions.Def_LimitsLifting_Approximation_CanonicalCover
import Definitions.Def_LimitsLifting_Approximation_RectangleScheme
open MultiplierAssoc206.Resolution

namespace LimitsLifting.Approximation

theorem proposition_4_5 {ι : Type} [Fintype ι] {Z : Set (ι → Bool)} (f : Z → Bool)
    (hf : PartialMonotone f) (A : ApproxModel Z) :
    A.mu f ≤ (monotoneSize f : ℝ) ∧ (A.IsNonMonotone → A.mu f ≤ (circuitSize f : ℝ)) := by sorry

end LimitsLifting.Approximation
