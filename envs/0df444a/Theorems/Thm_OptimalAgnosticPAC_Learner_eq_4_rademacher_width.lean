-- Prove2me | Theorems.Thm_OptimalAgnosticPAC_Learner_eq_4_rademacher_width
-- name    : OptimalAgnosticPAC.Learner.eq_4_rademacher_width
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:56:32.220008+00:00
-- url     : https://prove2.me/theorems/a85ff607-8a50-44b9-8a80-f1ae4a2d42e6
-- title:
--   Equation (4): $\mathfrak R_D(\mathcal F)\le 60\sqrt{d|D|}$
-- statement:
--   Let $P$ be a nonempty finite coordinate set, let $d\ge1$, and let $\mathcal F\subseteq\{-1,+1\}^P$ be nonempty with $\mathrm{VC}(\mathcal F)\le d$. For every $D\subseteq P$, the unnormalized signed Rademacher width of the projection of $\mathcal F$ to $D$ satisfies
--   $$\mathfrak R_D(\mathcal F)=\mathbb E_\varepsilon\max_{f\in\mathcal F}\sum_{p\in D}\varepsilon_pf(p)\le60\sqrt{d|D|}.$$
--
--   This is the only point at which the VC dimension enters the paper's argument. The paper obtains the constant from the chaining and covering arguments of Devroye and Lugosi.
--
--   Differences from the source:
--   - encoding: V_P = {−1,+1}^P with P a nonempty finite set → P : Type with Fintype and Nonempty, labelings P → Bool with true for +1, signed values through sgn; reason: the reused vcDim takes Bool-valued functions on a Type; renaming the two labels changes no quantity
--   - encoding: E_ε over uniform signs → the average over all ε : P → Bool; reason: the same finite expectation
-- source:
--   Dahl, Qian and Zhivotovskiy, An Optimal Agnostic PAC Algorithm, August 6, 2026 preprint, STOC 2027 submission #67, SHA-256 b61bab4e8b832787499a381cc9efadcf919f9384a3bcfae6c3412fb3e557e2fc, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/67.pdf, §2, equation (4), PDF p. 3 (printed p. 2)

import Mathlib
import Definitions.Def_HighDimProb_Chaining_VcDim
import Definitions.Def_OptimalAgnosticPAC_Learner_Cube
open scoped Classical

namespace OptimalAgnosticPAC.Learner

/-- Equation (4), PDF p. 3: `R_D(F) ≤ 60 √(d|D|)`. -/
theorem eq_4_rademacher_width {P : Type} [Fintype P] [Nonempty P] (d : ℕ) (hd : 1 ≤ d)
    (F : Set (P → Bool)) (hF : F.Nonempty) (hVC : HighDimProb.Chaining.vcDim F ≤ (d : ℕ∞))
    (D : Finset P) :
    width F D ≤ 60 * Real.sqrt ((d : ℝ) * (D.card : ℝ)) := by sorry

end OptimalAgnosticPAC.Learner
