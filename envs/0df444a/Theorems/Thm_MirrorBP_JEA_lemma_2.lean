-- Prove2me | Theorems.Thm_MirrorBP_JEA_lemma_2
-- name    : MirrorBP.JEA.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:58:31.911822+00:00
-- url     : https://prove2.me/theorems/b9fb0fe4-1d2d-4602-9012-4fff190eede8
-- title:
--   Lemma 2, p. 19 — W^SPP(φ) − g(y) ≤ −α(φ)·[max_j y_j − min_j y_j − 2m]⁺ (the bound on V₃, for every y)
-- statement:
--   Throughout, $V$ is a finite set of $m = |V| > 1$ nodes, $\mathcal T$ a finite set of demand types, each type $\tau$ has nonempty pick-up and drop-off neighborhoods $\mathcal P(\tau), \mathcal D(\tau) \subseteq V$, and the payoffs satisfy $|w_{j\tau k}| \le 1$ for $j \in \mathcal P(\tau)$, $k \in \mathcal D(\tau)$.
--
--   For every rate vector $\boldsymbol\phi$ and every $\mathbf y \in \mathbb R^V$,
--   $$W^{\mathrm{SPP}}(\boldsymbol\phi) - g(\mathbf y) \le -\alpha(\boldsymbol\phi)\cdot\Big[\max_{j\in V} y_j - \min_{j \in V} y_j - 2m\Big]^+ .$$
--   With $\mathbf y = \mathbf f(\bar{\mathbf q})$ this is the paper's bound $\mathcal V_3 \le -\alpha(\boldsymbol\phi)\,[\max_j f(\bar q_j) - \min_j f(\bar q_j) - 2m]^+$.
--
--   The dual gap is large when the congestion costs are spread out; Lemma 3 uses this to absorb $\mathcal V_2 + \mathcal V_4$.
--
--   Differences from the source:
--   - generalization: max_{τ, j ∈ P(τ), k ∈ D(τ)} |w_{jτk}| = 1 → |w j τ k| ≤ 1 for j ∈ P τ, k ∈ D τ; reason: the scaling is 'without loss of generality' (p. 10); every instance with max |w| = 1 satisfies |w| ≤ 1.
--   - reading: type set 𝒯 (finiteness implicit) → [Fintype Ty]; reason: the model is 'a finite-state Markov chain' and SPP 'a linear program' with sums over 𝒯 (pp. 9, 15); Appendix C's remark on infinitely many types presupposes finitely many in the model.
--   - generalization: y = f(q̄) for a strictly increasing C¹ congestion function f → every y : V → ℝ; reason: the bound involves f only through y = f(q̄); every such y is a special case.
--   - generalization: φ with α(φ) > 0 → any rate vector φ; reason: with α(φ) = 0 the statement is weak duality, which the paper's case includes.
-- source:
--   Kanoria, Qian, Blind Dynamic Resource Allocation in Closed Networks via Mirror Backpressure, arXiv:1903.02764v4, p. 19, Lemma 2; Appendix B.2, appendix pp. 7–8 (PDF 40–41)

import Mathlib
import Definitions.Def_MirrorBP_JEA_Model
import Definitions.Def_MirrorBP_JEA_SPP

namespace MirrorBP.JEA

open Finset

theorem lemma_2 {V Ty : Type} [Fintype V] [DecidableEq V] [Fintype Ty] [DecidableEq Ty]
    (P D : Ty → Finset V) (w : V → Ty → V → ℝ)
    (hm : 1 < Fintype.card V) (hP : ∀ τ, (P τ).Nonempty) (hD : ∀ τ, (D τ).Nonempty)
    (hw : ∀ τ, ∀ j ∈ P τ, ∀ k ∈ D τ, |w j τ k| ≤ 1)
    (φ : Ty → ℝ) (hφ : IsRate φ) (y : V → ℝ) :
    Wspp P D w φ - gDual P D w φ y
      ≤ -(alphaConn P D φ) * max 0 (ymax y - ymin y - 2 * (Fintype.card V : ℝ)) := by sorry

end MirrorBP.JEA
