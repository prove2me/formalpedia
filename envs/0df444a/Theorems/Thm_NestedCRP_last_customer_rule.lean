-- Prove2me | Theorems.Thm_NestedCRP_last_customer_rule
-- name    : NestedCRP.last_customer_rule
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:29:01.082596+00:00
-- url     : https://prove2.me/theorems/ed44ad10-209f-4c72-8785-f5da7a56b97d
-- title:
--   Last-customer rule for $p(c_d\mid c_{-d},\gamma)$
-- statement:
--   Let $T,T'$ be trees with the same restriction to the tourists other than $d$. Then
--
--   $$
--   \mathrm{ncrp}(T)\,\mathrm{last}(T',d)=\mathrm{ncrp}(T')\,\mathrm{last}(T,d),
--   $$
--
--   where $\mathrm{last}(T,d)$ is the mass of the path of $d$ when $d$ arrives last.
--
--   So, as a function of the path of $d$, the nested CRP mass is proportional to $\mathrm{last}(\cdot,d)$, which is the prior on paths in Eq. (4).
--
--   Differences from the source:
--   - reading: p(c_d | c_{-d}, γ) "as the prior on paths implied by the nested CRP" → the prior on paths is the last-arrival mass, and ncrp is proportional to it over trees with the same restriction; reason: the conditional of the law under exchangeability; this is the only meaning of the phrase
--   - encoding: a conditional probability → a cross-multiplied identity; reason: equivalent since all masses are positive; no division appears
-- source:
--   Blei–Griffiths–Jordan, The nested Chinese restaurant process and Bayesian nonparametric inference of topic hierarchies, J. ACM 57(2), Article 7 (2010), https://doi.org/10.1145/1667053.1667056, §5.2, p.7:17

import Mathlib
import Definitions.Def_NestedCRP_ncrpMass

namespace NestedCRP

/-- The last-customer rule: for trees with the same restriction to the tourists other than `d`,
the ratio of their nCRP masses is the ratio of `d`'s path masses as the last arrival. This is
`p(c_d | c_{-d}, γ)` as "the prior on paths implied by the nested CRP".
Blei–Griffiths–Jordan, *The nested Chinese restaurant process and Bayesian nonparametric
inference of topic hierarchies*, J. ACM 57(2), Article 7 (2010), §5.2, p.7:17. -/
theorem last_customer_rule {D : ℕ} {γ : ℝ} (hγ : 0 < γ) (d : Fin D) (T T' : Tree D)
    (h : T.AgreesOff d T') :
    ncrpMass γ T * lastMass γ T' d = ncrpMass γ T' * lastMass γ T d := by sorry

end NestedCRP
