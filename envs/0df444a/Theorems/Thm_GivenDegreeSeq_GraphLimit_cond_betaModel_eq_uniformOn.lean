-- Prove2me | Theorems.Thm_GivenDegreeSeq_GraphLimit_cond_betaModel_eq_uniformOn
-- name    : GivenDegreeSeq.GraphLimit.cond_betaModel_eq_uniformOn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:44:13.130035+00:00
-- url     : https://prove2.me/theorems/644f9d54-afe4-420e-b361-f3c88ec91477
-- title:
--   Proof of Theorem 1.1, p. 34 — the β-model conditioned on degree sequence $d$ is uniform on graphs with degree sequence $d$
-- statement:
--   Let $\beta\in\mathbb R^n$ and let $d$ be a valid degree sequence on $n$ vertices. Let $G'$ be a random graph drawn from the β-model $P_\beta$. Then, conditional on the event that $G'$ has degree sequence $d$, the law of $G'$ is the uniform distribution on the set of simple graphs with degree sequence $d$:
--   $$P_\beta\big(\,\cdot\mid \deg_{G'}=d\big)=\mathrm{Unif}\{G:\deg_G=d\}.$$
--
--   This is the link between the β-model and the uniform model $G_n$ of Theorem 1.1: tail bounds proved for $G'$ transfer to $G_n$ after dividing by $P_\beta(\deg_{G'}=d)$.
--
--   **Formalization Note** Conditioning is Mathlib's `ProbabilityTheory.cond` and the uniform law is `ProbabilityTheory.uniformOn`. The paper uses the statement for the MLE $\beta^n$; it is stated for every $\beta$, which costs nothing because $P_\beta(G)$ depends on $G$ only through its degrees.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, p. 34 (§6.2, proof of Theorem 1.1)

import Mathlib
import Definitions.Def_GivenDegreeSeq_Interior_IsGraphic
import Definitions.Def_GivenDegreeSeq_GraphLimit_EdgeModel

namespace GivenDegreeSeq.GraphLimit

/-- **Proof of Theorem 1.1, p. 34** (Chatterjee–Diaconis–Sly, arXiv:1005.1136v5). Conditional on
the event that its degree sequence equals a given valid degree sequence `d`, a graph drawn from
the β-model `P_β` is uniformly distributed on the simple graphs with degree sequence `d`. Stated
for every `β ∈ ℝⁿ` (the paper uses it for the MLE `βⁿ`); `P_β(G)` depends on `G` only through
its degree sequence. -/
theorem cond_betaModel_eq_uniformOn (n : ℕ) (β : Fin n → ℝ) (d : Fin n → ℕ) (hd : GivenDegreeSeq.Interior.IsGraphic d) :
    ProbabilityTheory.cond (betaModel β) (withDegrees d) =
      ProbabilityTheory.uniformOn (withDegrees d) := by sorry

end GivenDegreeSeq.GraphLimit
