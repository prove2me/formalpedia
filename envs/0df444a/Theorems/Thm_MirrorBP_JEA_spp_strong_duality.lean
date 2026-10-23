-- Prove2me | Theorems.Thm_MirrorBP_JEA_spp_strong_duality
-- name    : MirrorBP.JEA.spp_strong_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:58:32.323993+00:00
-- url     : https://prove2.me/theorems/837755b5-9a3d-4e01-8336-f3f31f865ae6
-- title:
--   Proof of Lemma 2, Appendix B.2, appendix p. 8, 'By strong duality we have min_y g(y) = W^SPP(φ)' — the dual g attains its minimum, equal to W^SPP(φ)
-- statement:
--   Throughout, $V$ is a finite set of $m = |V| > 1$ nodes, $\mathcal T$ a finite set of demand types, each type $\tau$ has nonempty pick-up and drop-off neighborhoods $\mathcal P(\tau), \mathcal D(\tau) \subseteq V$, and the payoffs satisfy $|w_{j\tau k}| \le 1$ for $j \in \mathcal P(\tau)$, $k \in \mathcal D(\tau)$.
--
--   For every rate vector $\boldsymbol\phi$, the dual function $g(\mathbf y) = \sum_\tau \phi_\tau \max_{j \in \mathcal P(\tau), k \in \mathcal D(\tau)} (w_{j\tau k} + y_j - y_k)^+$ of (15) attains its minimum over $\mathbf y \in \mathbb R^V$, and
--   $$\min_{\mathbf y} g(\mathbf y) = W^{\mathrm{SPP}}(\boldsymbol\phi).$$
--
--   This is the LP duality between SPP(φ) and its partial dual with the flow-balance constraints dualized; it is used in Lemma 2 and makes $\mathcal V_3 = W^{\mathrm{SPP}} - g(\mathbf f(\bar{\mathbf q}))$ nonpositive.
--
--   Differences from the source:
--   - generalization: max_{τ, j ∈ P(τ), k ∈ D(τ)} |w_{jτk}| = 1 → |w j τ k| ≤ 1 for j ∈ P τ, k ∈ D τ; reason: the scaling is 'without loss of generality' (p. 10); every instance with max |w| = 1 satisfies |w| ≤ 1.
--   - reading: type set 𝒯 (finiteness implicit) → [Fintype Ty]; reason: the model is 'a finite-state Markov chain' and SPP 'a linear program' with sums over 𝒯 (pp. 9, 15); Appendix C's remark on infinitely many types presupposes finitely many in the model.
--   - encoding: min_y g(y) = W^SPP(φ) → IsLeast (Set.range (gDual φ)) (Wspp φ); reason: 'min' asserts attainment and the value.
--   - generalization: φ with α(φ) > 0 (the setting of Lemma 2) → any rate vector φ; reason: the duality does not use connectedness.
-- source:
--   Kanoria, Qian, Blind Dynamic Resource Allocation in Closed Networks via Mirror Backpressure, arXiv:1903.02764v4, proof of Lemma 2, Appendix B.2, appendix p. 8 (PDF 41)

import Mathlib
import Definitions.Def_MirrorBP_JEA_Model
import Definitions.Def_MirrorBP_JEA_SPP

namespace MirrorBP.JEA

open Finset

theorem spp_strong_duality {V Ty : Type} [Fintype V] [DecidableEq V] [Fintype Ty] [DecidableEq Ty]
    (P D : Ty → Finset V) (w : V → Ty → V → ℝ)
    (hm : 1 < Fintype.card V) (hP : ∀ τ, (P τ).Nonempty) (hD : ∀ τ, (D τ).Nonempty)
    (hw : ∀ τ, ∀ j ∈ P τ, ∀ k ∈ D τ, |w j τ k| ≤ 1)
    (φ : Ty → ℝ) (hφ : IsRate φ) :
    IsLeast (Set.range (gDual P D w φ)) (Wspp P D w φ) := by sorry

end MirrorBP.JEA
