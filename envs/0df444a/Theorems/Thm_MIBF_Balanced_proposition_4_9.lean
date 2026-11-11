-- Prove2me | Theorems.Thm_MIBF_Balanced_proposition_4_9
-- name    : MIBF.Balanced.proposition_4_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:58:02.587802+00:00
-- url     : https://prove2.me/theorems/dfab5f78-de39-41bb-906a-c451ac5fbb0e
-- title:
--   Proposition 4.9 — tangent lower bound: a contact triple is unique and $\zeta(M)\ge p\,j(u,1-v)$, with equality when $pu\le\mu_u\le pu+1-p$
-- statement:
--   Natural logarithms; $h$ is the binary entropy in nats, $j$ the Jeffreys cost in nats and $\zeta$ the unrestricted edge value in nats (`zetaNat`). Let $M=(\mu_u,\mu_w,e_u,e_w)$ be a four-moment tuple ($0\le\mu_u,\mu_w\le1$, $0\le e_u\le h(\mu_u)$, $0\le e_w\le h(\mu_w)$) admitting a **contact triple** $(p,u,v)$ with $p\in(0,1]$, $u,v\in(0,\tfrac12)$ and
--   $$\mu_w-\mu_u=p\,(1-u-v),\qquad e_u=p\,h(u),\qquad e_w=p\,h(v). \qquad (30)$$
--   Then:
--   1. the triple is unique: any $(p',u',v')$ with $p'\in(0,1]$, $u',v'\in(0,\tfrac12)$ satisfying (30) equals $(p,u,v)$;
--   2. $$\zeta(M)\ \ge\ L_{3b}(M):=p\,j(u,1-v);$$
--   3. equality $\zeta(M)=p\,j(u,1-v)$ holds whenever $pu\le\mu_u\le pu+1-p$.
--
--   The bound is realised by a three-atom law on $(0,0)$, $(u,1-v)$, $(1,1)$; it is the tangent bound used for cross-half and extreme-boundary tuples in the small-boundary theorem.
--
--   **Formalization Note** The comparison is in the extended reals ($\zeta\in[0,+\infty]$).
--
--   Differences from the source:
--   - reading: "Suppose $M=(\mu_u,\mu_w,e_u,e_w)$ admits a triple" → hypothesis that $M$ is a four-moment tuple (nats); reason: $M$ denotes a four-moment tuple in the paper's notation (Definition 2.1).
--   - reading: "the triple is unique" → every triple in the same ranges satisfying (30) equals $(p,u,v)$; reason: uniqueness among the triples the statement quantifies over.
--   - encoding: $\zeta(M)\in[0,+\infty]$ compared with a real number → comparison of `zetaNat` and $p\,j(u,1-v)$ in `EReal`; reason: Lean convention; same instances.
-- source:
--   Chen, Gohari, Javanmard, Lin, Mirrokni, Nair, Woodruff, A Proof of the Most Informative Boolean Function Conjecture, arXiv:2609.24931 (held version, sha256 35793b82…1f9f), p. 13, Proposition 4.9, eqs. (30)–(31)

import Mathlib
import Definitions.Def_MIBF_Balanced_EdgeValue

namespace MIBF.Balanced
theorem proposition_4_9 (mu mw eu ew p u v : ℝ) (hM : IsFourMomentTupleNat mu mw eu ew)
    (hp : 0 < p ∧ p ≤ 1) (hu : 0 < u ∧ u < 1 / 2) (hv : 0 < v ∧ v < 1 / 2)
    (h30_1 : mw - mu = p * (1 - u - v)) (h30_2 : eu = p * Real.binEntropy u)
    (h30_3 : ew = p * Real.binEntropy v) :
    (∀ p' u' v' : ℝ, (0 < p' ∧ p' ≤ 1) → (0 < u' ∧ u' < 1 / 2) → (0 < v' ∧ v' < 1 / 2) →
        mw - mu = p' * (1 - u' - v') → eu = p' * Real.binEntropy u' →
        ew = p' * Real.binEntropy v' → p' = p ∧ u' = u ∧ v' = v) ∧
      ((p * natInteriorCost u (1 - v) : ℝ) : EReal) ≤ ((zetaNat mu mw eu ew : ENNReal) : EReal) ∧
      (p * u ≤ mu → mu ≤ p * u + 1 - p →
        ((zetaNat mu mw eu ew : ENNReal) : EReal) = ((p * natInteriorCost u (1 - v) : ℝ) : EReal)) := by sorry
end MIBF.Balanced
