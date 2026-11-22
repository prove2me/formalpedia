-- Prove2me | Theorems.Thm_NConjecture_abc_exponent_sharp
-- name    : NConjecture.abc_exponent_sharp
-- status  : Proved
-- author  : @LG
-- created : 2026-11-22T00:43:26.860312+00:00
-- url     : https://prove2.me/theorems/3e665518-08c4-43ca-943a-41d33b795a7f
-- title:
--   Sharpness of the abc exponent ($\limsup L_3 \ge 1$)
-- statement:
--   Browkin–Brzeziński (§1, p. 931) observe that the abc exponent $1$ is sharp: "it is not difficult to show that there is a limit point of this set which is $\ge 1$," i.e. $\limsup L(a,b,c)\ge 1$ over coprime triples. In $\varepsilon$-form this says that for every $\varepsilon>0$ there are infinitely many coprime positive triples $a+b=c$ whose quality exceeds $1-\varepsilon$:
--   $$\#\{(a,b,c): a,b>0,\ \gcd(a,b)=1,\ a+b=c,\ c>\operatorname{rad}(abc)^{\,1-\varepsilon}\}=\infty.$$
--   Here $\operatorname{rad}(abc)$ is the product of the distinct primes dividing $abc$. An explicit witness family is $(1,\,9^k-1,\,9^k)$, whose quality is $>1$ for every $k$ (Ramaekers, §1.1). This is the $n=3$ base case of the sharp lower bound $\limsup L_n\ge 2n-5$.
--
--   **Formalization Note.** A triple is stored as $t=(a,b,c)\in\mathbb N^3$ with $c=t.2.2$; the radical is `Brocard.radical`. The strict inequality $c>\operatorname{rad}(abc)^{1-\varepsilon}$ is equivalent to $L>1-\varepsilon$ because $\operatorname{rad}(abc)\ge 2$.
-- source:
--   J. Browkin, J. Brzeziński, Some remarks on the abc-conjecture, Math. Comp. 62(206) (1994), 931–939. https://cr.yp.to/bib/1994/browkin.pdf §1 pp. 931–932 (limit point ≥ 1). Explicit family: C. Ramaekers, The abc-conjecture and the n-conjecture, TU/e (2009), §1.1. https://pure.tue.nl/ws/portalfiles/portal/67739846/657782-1.pdf

import Mathlib
import Definitions.Def_Brocard_Defs

namespace NConjecture

theorem abc_exponent_sharp (ε : ℝ) (hε : 0 < ε) :
    Set.Infinite {t : ℕ × ℕ × ℕ | 0 < t.1 ∧ 0 < t.2.1 ∧ Nat.Coprime t.1 t.2.1 ∧
      t.1 + t.2.1 = t.2.2 ∧
      (Brocard.radical (t.1 * t.2.1 * t.2.2) : ℝ) ^ (1 - ε) < (t.2.2 : ℝ)} := by sorry

end NConjecture
