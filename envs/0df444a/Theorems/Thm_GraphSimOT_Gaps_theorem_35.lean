-- Prove2me | Theorems.Thm_GraphSimOT_Gaps_theorem_35
-- name    : GraphSimOT.Gaps.theorem_35
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:08:00.285375+00:00
-- url     : https://prove2.me/theorems/ca75022b-fb7d-4340-9398-c203eaa36de9
-- title:
--   Theorem 35 — every Q ∈ DS(n) admits a C_thin ln(2n) ln ln(4n)-thin permutation matrix [HOG26]
-- statement:
--   There is an absolute constant $C_{thin}>0$ such that for every $n\ge2$ (the standing assumption of App. E.2) every doubly stochastic $Q\in\mathrm{DS}(n)$ admits a permutation matrix $P$ that is $\alpha$-thin with respect to $Q$ for some
--   $$\alpha\ \le\ C_{thin}\,\ln(2n)\,\ln\ln(4n),$$
--   where $P$ is $\alpha$-thin ($\alpha>0$) if for all $X, Y\subseteq[n]$ the weight of $P$ across the cut $(X\times\bar Y)\cup(\bar X\times Y)$ is at most $\alpha$ times the weight of $Q$ across it (Eq. (23)).
--
--   The paper cites this thin-perfect-matching theorem of Haqi and Oveis Gharan [HOG26, Theorem 1.4]; it drives the multiplicative rounding of Theorem 38.
--
--   Differences from the source:
--   - encoding: every Q ∈ DS(n) admits an α-thin permutation matrix with respect to Q with α ≤ C_thin ln(2n) ln ln(4n) → IsThinConstant Cthin: ∀ n ≥ 2, ∀ Q ∈ doublyStochastic ℝ (Fin n), ∃ α ≤ Cthin * log (2n) * log (log (4n)), ∃ π, IsThin α (π.permMatrix ℝ) Q; reason: IsThin includes α > 0 (the definition of thinness starts 'Let α > 0'); n ≥ 2 is the standing assumption of App. E.2
--   - encoding: indices in [n] = {1, …, n} → Fin n = {0, …, n − 1}; reason: relabelling of the index set; no instance changes
-- source:
--   Breitung, Gervens, Grohe, Graph Similarity Meets Optimal Transport, arXiv:2611.05048 (held version, sha256 1cd10e91…), p. 32, Theorem 35 ([HOG26, Theorem 1.4])

import Mathlib
import Definitions.Def_GraphSimOT_Gaps_CutRounding

namespace GraphSimOT.Gaps

/-- Theorem 35 (App. E.2, p. 32; [HOG26, Theorem 1.4]): there is an absolute constant
`C_thin > 0` such that every `Q ∈ DS(n)` (`n ≥ 2`, App. E.2) admits an `α`-thin permutation
matrix with respect to `Q` with `α ≤ C_thin ln(2n) ln ln(4n)`. -/
theorem theorem_35 : ∃ Cthin : ℝ, 0 < Cthin ∧ IsThinConstant Cthin := by sorry

end GraphSimOT.Gaps
