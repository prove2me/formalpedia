-- Prove2me | Theorems.Thm_HeilmanMax3Cut_im12_step
-- name    : HeilmanMax3Cut.im12_step
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:29:23.302988+00:00
-- url     : https://prove2.me/theorems/32f4ddfb-0f9e-4bad-b4c6-49b8855a049f
-- title:
--   p.4, [IM12] sentence — Standard Simplex at $\rho=-1/2$ gives MAX-3-CUT hardness
-- statement:
--   Assume that for every $n\ge2$ and every partition $\Omega$ of $\mathbb R^n$ into three measurable sets, $Q^{(n)}_{-1/2}(\Omega,\Omega)\ge Q^{(2)}_{-1/2}(\Theta,\Theta)$ (the inequality of Theorem 1.2 at $\rho=-1/2$), and assume the Unique Games Conjecture. Then for every $\varepsilon>0$ there are $c>0$ and $s$ with
--
--   $$\frac sc\ \le\ r(-1/2)+\varepsilon,\qquad r(\rho)=\frac{\tfrac32\bigl[1-3\bigl(\tfrac19+\frac{[\arccos(-\rho)]^2-[\arccos(\rho/2)]^2}{4\pi^2}\bigr)\bigr]}{1-\rho},$$
--
--   such that MAX-3-CUT on weighted graphs is $(c,s)$-hard.
--
--   The paper attributes this implication to S. Isaksson and E. Mossel, *Maximally stable Gaussian partitions with discrete applications*, Israel J. Math. 189 (2012) [IM12], via the reduction of Khot–Kindler–Mossel–O'Donnell [KKMO07].
--
--   Differences from the source:
--   - reading: "Theorem 1.2 or 1.3 with ρ = −1/2 implies our first main application" → hypothesis: the minimizing inequality of Theorem 1.2 at ρ = −1/2 for every n ≥ 2 and partition; conclusion: weighted (c, s)-hardness with s/c ≤ r(−1/2) + ε; reason: the minimizing clause of Theorem 1.2 at ρ = −1/2 is this inequality; [IM12]'s reduction yields gap hardness on weighted instances with ratio the Frieze–Jerrum expression at ρ = −1/2, which is α₃ by (2) and transfers to simple graphs by [CST01]
--   - encoding: Ω a measurable partition → IsPartition Ω in the hypothesis; reason: Q does not see null sets and every a.e.-partition agrees with an exact one up to a null set, so the hypothesis is equivalent to the one over exact partitions
--   - reading: the Unique Games Conjecture [Kho02, KN10] (paraphrased on p.5 in the linear-equations form) → the published OptInapprox.MaxCut.UGC (Khot's Unique Label Cover form); reason: Theorem 1.4 cites [Kho02, KN10], where the conjecture is stated for Unique Label Cover
--   - encoding: NP-hard to approximate MAX-3-CUT within r(−1/2) + ε → ∃ c > 0, s with s/c ≤ r(−1/2) + ε and (c, s)-gap NP-hardness, both promise sets restricted to graphs with at least one edge (Max3CutHard.MaxKCutHard 3, ℕ-weighted graphs); reason: (c, s)-hardness is the form the reductions produce, and it implies NP-hardness of approximation within s/c; the clause 0 < w(G) in both promise sets (inherited from the published Max3CutHard.MaxKCutHard) only excludes the edgeless graph, on which both promises hold
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), p.4 ("As shown in [IM12], Theorem 1.2 or 1.3 with ρ = −1/2 implies our first main application")

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OptInapprox_MaxCut_UGC
import Definitions.Def_Max3CutHard_MaxKCutHard
import Definitions.Def_HeilmanMax3Cut_Qstab
import Definitions.Def_HeilmanMax3Cut_Theta
import Definitions.Def_HeilmanMax3Cut_fjRatio
open OAI.GaussianPropeller OptInapprox.MaxCut

namespace HeilmanMax3Cut

/-- **The [IM12] step: the Standard Simplex inequality at `ρ = −1/2` gives MAX-3-CUT hardness.**
Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), p.4: "As shown in [IM12], Theorem 1.2 or 1.3 with `ρ = −1/2` implies our first main
application." [IM12] is S. Isaksson and E. Mossel, *Maximally stable Gaussian partitions with
discrete applications*, Israel J. Math. 189 (2012), building on the reduction of
Khot–Kindler–Mossel–O'Donnell [KKMO07].

If the three 120° sectors minimize noise stability at correlation `ρ = −1/2` among three-set
partitions of every `ℝⁿ`, `n ≥ 2` (the inequality of Theorem 1.2 at `ρ = −1/2`), and the Unique
Games Conjecture holds, then for every `ε > 0` there are `c > 0` and `s` with
`s/c ≤ r(−1/2) + ε` such that MAX-3-CUT is `(c, s)`-hard, where `r` is the Frieze–Jerrum ratio
function of (2).

**Formalization Note.** The UGC is the published `OptInapprox.MaxCut.UGC` (Khot's Unique Label
Cover form). `(c, s)`-hardness is the published `Max3CutHard.MaxKCutHard 3 c s` (ℕ-weighted
graphs), the conclusion [IM12]/[KKMO07]'s reduction produces; "NP-hard to approximate within `r`"
is encoded as `∃ c > 0, s, s/c ≤ r + ε` with `(c, s)`-hardness. -/
theorem im12_step
    (hSS : ∀ n : ℕ, 2 ≤ n → ∀ Ω : Fin 3 → Set (Space n), IsPartition Ω →
      Qstab 2 (-1 / 2) Theta Theta ≤ Qstab n (-1 / 2) Ω Ω)
    (hUGC : UGC) :
    ∀ ε : ℝ, 0 < ε → ∃ c s : ℝ, 0 < c ∧ s / c ≤ fjRatio (-1 / 2) + ε ∧
      Max3CutHard.MaxKCutHard 3 c s := by sorry

end HeilmanMax3Cut
