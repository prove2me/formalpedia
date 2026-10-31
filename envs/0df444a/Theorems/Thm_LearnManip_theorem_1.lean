-- Prove2me | Theorems.Thm_LearnManip_theorem_1
-- name    : LearnManip.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:01:34.486282+00:00
-- url     : https://prove2.me/theorems/ba36e682-49b2-48ac-b8db-ca6097b2875e
-- title:
--   Theorem 1, p.15 — $q^*$ and the closed form of $G$
-- statement:
--   Let $\bar\eta=\min(\eta,1)$, $s_{TH}(c)=\sqrt{2\gamma c(1-\alpha)(1-\alpha\bar\eta)}$ and $\kappa(s,c)=\min\{j\in\mathbb N:s>s_{TH}(c\bar\eta^{\,j-1})\}$. The function
--   $$G(s,c)=\alpha^{\kappa-1}\Biggl(\frac{c\bar\eta^{\,\kappa-1}}{s}+\frac{s}{2\gamma(1-\alpha)^2}-2\sqrt{\frac{c\bar\eta^{\,\kappa-1}(1-\alpha\bar\eta)}{2\gamma(1-\alpha\sqrt{\bar\eta})^2(1-\alpha)}}\Biggr),$$
--   with $G=0$ when no $\kappa$ exists, is in the growth class and solves (15), for every $\eta\ge0$, with the true $\eta$ in $c\mapsto c\eta$. It is the only solution in that class. For $c>0$,
--   $$q^*(s,c)=\Bigl(\frac1{s_{TH}(c)}-\frac1s\Bigr)^+$$
--   is the unique maximizer of the objective of (15).
--
--   The theorem says that the firm disseminates only above a threshold in the variance, and then brings the variance down to the threshold.
--
--   Differences from the source:
--   - encoding: two regimes, η ≤ 1 and η > 1 (the degenerate case of η = 1) → one statement with η̄ = min(η, 1) in s_TH, κ, G, q*; reason: the printed reduction says exactly this; the objective keeps the true η
--   - reading: (unique) → unique maximizer of (15) for c > 0, and unique solution of (15) in the growth class; reason: at c = 0 the paper has q* = ∞ (p.33), which is not in ℝ₊, and without a class the solution of the recursion is not unique
--   - reading: κ = min of a possibly empty set → G = 0 when the set is empty; reason: footnote 9, p.19, has κ = ∞, and (18) at κ = ∞ is its limit 0
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), Theorem 1, p.15

import Mathlib
import Definitions.Def_LearnManip_Params
import Definitions.Def_LearnManip_manipObjective
import Definitions.Def_LearnManip_IsManipValue
import Definitions.Def_LearnManip_GClass
import Definitions.Def_LearnManip_Gclosed
import Definitions.Def_LearnManip_qStar

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory InformationTheory Filter

namespace LearnManip

/-- Theorem 1, p.15, of Keppo, Kim, Zhang (SSRN 3465030, 2021-09-04): the closed form `G` of (18), with
`η̄ = min(η, 1)`, is in the growth class and solves (15), for every `η ≥ 0`; it is the only solution in
that class; and for `c > 0`, `q*(s, c)` of (17) is the unique maximizer of the objective of (15).

**Formalization Note.** The regimes `η ≤ 1` and `η > 1` are one statement through `effEta`, inside
`sTH`, `Gclosed` and `qStar`, while the objective keeps the true `η`; that is the last sentence of the
theorem. "Unique" is read as unique in this class. At `c = 0` no maximizer exists (`q* = ∞`, p.33). -/
theorem theorem_1 (P : Params) :
    (GClass (Gclosed P) ∧ IsManipValue P (Gclosed P)) ∧
    (∀ g : ℝ≥0 → ℝ≥0 → ℝ, GClass g → IsManipValue P g → ∀ s c : ℝ≥0, g s c = Gclosed P s c) ∧
    ∀ s c : ℝ≥0, 0 < c →
      manipObjective P (Gclosed P) s c (qStar P s c) = Gclosed P s c ∧
      ∀ q : ℝ≥0, manipObjective P (Gclosed P) s c q = Gclosed P s c → q = qStar P s c := by sorry

end LearnManip
