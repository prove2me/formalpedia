-- Prove2me | Theorems.Thm_OnlineCAP_theorem_4_1
-- name    : OnlineCAP.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:27:24.411697+00:00
-- url     : https://prove2.me/theorems/eaee812f-e726-467d-bd35-b32e923b8962
-- title:
--   Theorem 4.1 — a ρ(n)-competitive fractional algorithm gives an O(ρ(n) log log n)-competitive randomized one for TL-rectangle hitting set
-- statement:
--   There is a function $\beta(n)=O(\log\log n)$ such that the following holds for every finite point set $P\subseteq\mathbb R^2$ with $n=|P|$, every nonnegative cost function $c$ on $P$, and every $\rho\in\mathbb R$. If weighted online TL-rectangle hitting set on $(P,c)$ has a $\rho$-competitive online fractional algorithm, then it has a randomized online algorithm, feasible for every outcome of its coins, with
--   $$\mathbb E[c(F_t)]\le\rho\,\beta(n)\cdot\mathrm{OPT}$$
--   on every valid sequence of TL shapes, against an oblivious adversary.
--
--   For a ratio function $\rho(n)$ this is the expected competitive ratio $O(\rho(n)\log\log n)$, with an $O$-constant independent of $\rho$.
--
--   Differences from the source:
--   - generalization: a ρ(n)-competitive fractional algorithm for the problem → for each instance (P, c) and each real ρ, a ρ-competitive fractional algorithm for that instance; reason: the source's statement follows with ρ = ρ(|P|), since the ratio ρ · β(n) is O(ρ(n) log log n) with a constant independent of ρ
--   - reading: online TL-rectangle hitting set → the weighted problem, every cost function c ≥ 0 on P (unit costs included); reason: §4 treats weighted hitting set ("non-negative costs c_p", p.15) and the proof bounds E[c(H)] = Σ c_p Pr[p ∈ H]
--   - encoding: expected competitive ratio O(ρ(n) log log n) → ρ · β(n) with β =O[atTop] log log n, in expectation against the integral offline optimum OPT; reason: §2.2 measures randomized algorithms against OPT, the integral optimum; natural logarithms
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), Theorem 4.1, p.13 (proof p.21)

import Mathlib
import Definitions.Def_OnlineCAP_RandOnlineAlg
import Definitions.Def_OnlineCAP_OnlineHSInstance
import Definitions.Def_OnlineCAP_OnlineHSInstance_OPT
import Definitions.Def_OnlineCAP_IsCompetitive
import Definitions.Def_OnlineCAP_IsLeftless
import Definitions.Def_OnlineCAP_IsTopless
import Definitions.Def_OnlineCAP_IsTLShape
import Definitions.Def_OnlineCAP_tlInstance
import Definitions.Def_OnlineCAP_FracOnlineAlg
import Definitions.Def_OnlineCAP_OnlineHSInstance_OPTfrac
import Definitions.Def_OnlineCAP_IsFracCompetitive

open MeasureTheory Filter Asymptotics

namespace OnlineCAP

/-- **Theorem 4.1 (rounding fractional TL-rectangle hitting set).** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), Theorem 4.1, p.13 (PDF
p.13): "If there exists a ρ(n)-competitive fractional algorithm for online TL-rectangle hitting
set, then there exists a randomized online algorithm for online TL-rectangle hitting set with
expected competitive ratio O(ρ(n) log log n)." Here n is "the number of points in the instance"
(p.13).

There is a function `β(n) = O(log log n)` such that for every finite point set `P ⊆ ℝ²` with
`n = |P|`, every nonnegative cost function `c` on `P` and every real `ρ`: if the weighted online
TL-rectangle hitting set instance `(P, c)` has a `ρ`-competitive online fractional algorithm, then
it has a randomized online algorithm that is `ρ · β(n)`-competitive in expectation (against the
integral offline optimum).

**Formalization Note.** Stated per instance, with the fractional ratio a number `ρ`; for a ratio
function `ρ(n)` it gives the ratio `ρ(n) β(n) = O(ρ(n) log log n)`, with an `O`-constant that does
not depend on `ρ`. -/
theorem theorem_4_1 : ∃ β : ℕ → ℝ, β =O[atTop] (fun n : ℕ => Real.log (Real.log n)) ∧
    ∀ (P : Finset (ℝ × ℝ)) (c : ℝ × ℝ → ℝ), (∀ p ∈ P, 0 ≤ c p) → ∀ ρ : ℝ,
      (∃ X : FracOnlineAlg (ℝ × ℝ) (Set (ℝ × ℝ)), IsFracCompetitive (tlInstance P c) X ρ) →
      ∃ A : RandOnlineAlg (ℝ × ℝ) (Set (ℝ × ℝ)),
        IsCompetitive (tlInstance P c) A (ρ * β P.card) := by sorry

end OnlineCAP
