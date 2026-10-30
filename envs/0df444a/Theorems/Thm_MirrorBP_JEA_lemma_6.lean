-- Prove2me | Theorems.Thm_MirrorBP_JEA_lemma_6
-- name    : MirrorBP.JEA.lemma_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:58:28.784625+00:00
-- url     : https://prove2.me/theorems/aa35442f-4b14-495f-b427-d9c79b04cf01
-- title:
--   Lemma 6, Appendix A, appendix p. 3 — the value of the relaxed LP (29), (31), (32) is at most W^SPP(φ̄) + mK/T
-- statement:
--   Throughout, $V$ is a finite set of $m = |V| > 1$ nodes, $\mathcal T$ a finite set of demand types, each type $\tau$ has nonempty pick-up and drop-off neighborhoods $\mathcal P(\tau), \mathcal D(\tau) \subseteq V$, and the payoffs satisfy $|w_{j\tau k}| \le 1$ for $j \in \mathcal P(\tau)$, $k \in \mathcal D(\tau)$.
--
--   For every nonnegative vector $\boldsymbol\phi$ on $\mathcal T$ and every slack $r \ge 0$, the value of the LP that maximizes (29) subject to the demand constraint (31) and the approximate flow balance (32) with slack $r$ satisfies
--   $$\mathrm{val} \le W^{\mathrm{SPP}}(\boldsymbol\phi) + m\, r.$$
--   The paper's case is $\boldsymbol\phi = \bar{\boldsymbol\phi}$, $r = K/T$, giving $W^{\mathrm{SPP}}(\bar{\boldsymbol\phi}) + mK/T$.
--
--   With Lemma 4 this gives Proposition 1.
--
--   Differences from the source:
--   - generalization: max_{τ, j ∈ P(τ), k ∈ D(τ)} |w_{jτk}| = 1 → |w j τ k| ≤ 1 for j ∈ P τ, k ∈ D τ; reason: the scaling is 'without loss of generality' (p. 10); every instance with max |w| = 1 satisfies |w| ≤ 1.
--   - reading: type set 𝒯 (finiteness implicit) → [Fintype Ty]; reason: the model is 'a finite-state Markov chain' and SPP 'a linear program' with sums over 𝒯 (pp. 9, 15); Appendix C's remark on infinitely many types presupposes finitely many in the model.
--   - generalization: φ = φ̄ and slack K/T → any φ ≥ 0 and any r ≥ 0; reason: φ̄ of rate vectors is nonnegative and K/T ≥ 0, so the paper's statement is a special case.
--   - encoding: W^SPP(φ̄) as the value of the flow form (29)–(31) → Wspp, the value of the fraction form (11)–(13); reason: the paper states that the two forms are the same LP under z = φx (PDF 34).
-- source:
--   Kanoria, Qian, Blind Dynamic Resource Allocation in Closed Networks via Mirror Backpressure, arXiv:1903.02764v4, Appendix A, appendix p. 3 (PDF 36), Lemma 6

import Mathlib
import Definitions.Def_MirrorBP_JEA_Model
import Definitions.Def_MirrorBP_JEA_SPP

namespace MirrorBP.JEA

open Finset

theorem lemma_6 {V Ty : Type} [Fintype V] [DecidableEq V] [Fintype Ty] [DecidableEq Ty]
    (P D : Ty → Finset V) (w : V → Ty → V → ℝ)
    (hm : 1 < Fintype.card V) (hP : ∀ τ, (P τ).Nonempty) (hD : ∀ τ, (D τ).Nonempty)
    (hw : ∀ τ, ∀ j ∈ P τ, ∀ k ∈ D τ, |w j τ k| ≤ 1)
    (φ : Ty → ℝ) (hφ : ∀ τ, 0 ≤ φ τ) (r : ℝ) (hr : 0 ≤ r) :
    relaxedValue P D w φ r ≤ Wspp P D w φ + (Fintype.card V : ℝ) * r := by sorry

end MirrorBP.JEA
