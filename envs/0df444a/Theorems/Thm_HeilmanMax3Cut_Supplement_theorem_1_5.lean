-- Prove2me | Theorems.Thm_HeilmanMax3Cut_Supplement_theorem_1_5
-- name    : HeilmanMax3Cut.Supplement.theorem_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:07:19.609204+00:00
-- url     : https://prove2.me/theorems/0d5e1aa2-2b79-451d-9ee1-87ae20933ff3
-- title:
--   Theorem 1.5 — UG-hardness of MAX-2-LIN(3): gap $3/5-\varepsilon$ vs. $\mathrm{Stab}_{2/5}(\mathrm{Plur}_3)+\varepsilon$, ratio $\alpha_{\mathrm{2LIN}(3)}+\varepsilon$
-- statement:
--   Assume the Unique Games Conjecture. Then for every $\varepsilon>0$:
--
--   1. it is NP-hard to distinguish instances $I$ of MAX-2-LIN(3) with $\mathrm{OPT}(I)\ge\frac35-\varepsilon$ from instances with
--   $$\mathrm{OPT}(I)\le\frac13+\frac{3}{4\pi^2}\Big(\arccos(-2/5)^2-\arccos(1/5)^2\Big)+\varepsilon;$$
--   2. consequently it is NP-hard to approximate MAX-2-LIN(3) within $\alpha_{\mathrm{2LIN}(3)}+\varepsilon$, where
--   $$\alpha_{\mathrm{2LIN}(3)}=\frac59+\frac{5}{4\pi^2}\Big(\arccos(-2/5)^2-\arccos(1/5)^2\Big)\approx0.815723527338279;$$
--
--   and both hold even when every equation has the form $x_i-x_j=c \bmod 3$. Here $\mathrm{OPT}(I)$ is the largest fraction of the equations of $I$ satisfied by an assignment in $(\mathbb Z/3)^n$.
--
--   This is the best known hardness of approximation for MAX-2-LIN(3).
--
--   **Formalization Note** "NP-hard to approximate within $r$" is the existence of $c>0$ and $s$ with $s/c\le r$ such that the $(c,s)$ gap problem is NP-hard. Instances are lists of difference equations with $i\ne j$.
--
--   Differences from the source:
--   - reading: the Unique Games Conjecture (paraphrased on p.5 in the linear-equations form) → the published OptInapprox.MaxCut.UGC (Khot's Unique Label Cover form); reason: the paper cites the conjecture of [Kho02, KN10], stated there for Unique Label Cover; the same reading as the published goal HeilmanMax3Cut.theorem_1_4
--   - encoding: instances of MAX-2-LIN(3) (two-term linear equations over the field of three elements); the result holds even when every equation has the form x_i − x_j = c mod 3 → Lin2Inst: lists, with repetitions, of equations x_i − x_j = c with i ≠ j (both clauses stated on this class); reason: the theorem's last sentence asserts both clauses on this class, and hardness on it implies hardness for all two-term equations; an equation with i = j is not two-term
--   - encoding: OPT(I) of any instance → both promise sets require a nonempty list of equations; reason: OPT is a fraction of the m equations and is undefined at m = 0; the clause only excludes that instance
--   - encoding: NP-hard to approximate MAX-2-LIN(3) within α_2LIN(3) + ε → ∃ c > 0, s with s/c ≤ α_2LIN(3) + ε and the (c, s) gap problem NP-hard; reason: the form the reduction produces (c = 3/5 − ε′, s the soundness), implying NP-hardness of approximation within s/c; as in the published goal
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Theorem 1.5, p.4 (proof App. B, p.43)

import Mathlib
import Definitions.Def_SetCoverThreshold_SetCover_Complexity
import Definitions.Def_OptInapprox_MaxCut_UGC
import Definitions.Def_HeilmanMax3Cut_Supplement_lin2OPT
import Definitions.Def_HeilmanMax3Cut_Supplement_encLin2
open OptInapprox.MaxCut Real

namespace HeilmanMax3Cut.Supplement

/-- **Theorem 1.5 (Hardness for MAX-2-LIN(3)).** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Theorem 1.5, p.4: "Assume the Unique Games
Conjecture. Then, for every `ε > 0`, it is NP-hard to distinguish instances `I` of MAX-2-LIN(3)
satisfying `OPT(I) ≥ 3/5 − ε` from those satisfying
`OPT(I) ≤ 1/3 + 3/(4π²)(arccos(−2/5)² − arccos(1/5)²) + ε`. Consequently, assuming the Unique Games
Conjecture, it is NP-hard to approximate MAX-2-LIN(3) within a multiplicative factor of
`α_2LIN(3) + ε` … The result holds even when every equation has the form `x_i − x_j = c mod 3`.
Here … `α_2LIN(3) := 5/9 + 5/(4π²)(arccos(−2/5)² − arccos(1/5)²)`."

**Formalization Note.** The UGC is the published `OptInapprox.MaxCut.UGC`; "NP-hard to distinguish"
is the published `SetCoverThreshold.SetCover.GapNPHard` over the injective unary encoding `encLin2`.
Instances are lists of difference equations `x_i − x_j = c` (`Lin2Inst`), so both clauses are stated
on the subclass of the last sentence, which implies them for general two-term equations. Both
promise sets require a nonempty list (the fraction `OPT` is undefined for `m = 0`). "NP-hard to
approximate within `r`" is: there are `c > 0` and `s` with `s/c ≤ r` and the `(c, s)`-gap problem
NP-hard, as in the published goal `HeilmanMax3Cut.theorem_1_4`. -/
theorem theorem_1_5 (hUGC : UGC) :
    (∀ ε : ℝ, 0 < ε →
      SetCoverThreshold.SetCover.GapNPHard encLin2
        (fun I : Lin2Inst => I.eqs ≠ [] ∧ 3 / 5 - ε ≤ lin2OPT I)
        (fun I : Lin2Inst => I.eqs ≠ [] ∧
          lin2OPT I ≤ 1 / 3 + 3 / (4 * π ^ 2) * (arccos (-2 / 5) ^ 2 - arccos (1 / 5) ^ 2) + ε)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ c s : ℝ, 0 < c ∧
      s / c ≤ 5 / 9 + 5 / (4 * π ^ 2) * (arccos (-2 / 5) ^ 2 - arccos (1 / 5) ^ 2) + ε ∧
      SetCoverThreshold.SetCover.GapNPHard encLin2
        (fun I : Lin2Inst => I.eqs ≠ [] ∧ c ≤ lin2OPT I)
        (fun I : Lin2Inst => I.eqs ≠ [] ∧ lin2OPT I ≤ s)) := by sorry

end HeilmanMax3Cut.Supplement
