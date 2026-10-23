-- Prove2me | Theorems.Thm_MirrorBP_JEA_lemma_5
-- name    : MirrorBP.JEA.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:58:29.835512+00:00
-- url     : https://prove2.me/theorems/d4af8c57-c4bd-4b92-867b-ddb243a20d73
-- title:
--   Lemma 5, Appendix A, appendix p. 3 — a solution of the relaxed LP splits as z^S + z^DAG, z^S exactly balanced and z^DAG acyclic
-- statement:
--   Throughout, $V$ is a finite set of $m = |V| > 1$ nodes, $\mathcal T$ a finite set of demand types, each type $\tau$ has nonempty pick-up and drop-off neighborhoods $\mathcal P(\tau), \mathcal D(\tau) \subseteq V$, and the payoffs satisfy $|w_{j\tau k}| \le 1$ for $j \in \mathcal P(\tau)$, $k \in \mathcal D(\tau)$.
--
--   Let $\boldsymbol\phi$ be a vector on $\mathcal T$ and $r$ a real number. Every flow $\mathbf z^{\mathrm F}$ satisfying the demand constraint (31) and the approximate flow balance (32) with slack $r$ decomposes as
--   $$\mathbf z^{\mathrm F} = \mathbf z^{\mathrm S} + \mathbf z^{\mathrm{DAG}} \qquad (33)$$
--   where $\mathbf z^{\mathrm S}$ satisfies exact flow balance (30) and (31), and $\mathbf z^{\mathrm{DAG}}$ is an acyclic flow satisfying (32) and (31).
--
--   The decomposition separates the circulating part of a flow, which SPP can carry, from the acyclic part, whose payoff Lemma 6 bounds.
--
--   Differences from the source:
--   - generalization: max_{τ, j ∈ P(τ), k ∈ D(τ)} |w_{jτk}| = 1 → |w j τ k| ≤ 1 for j ∈ P τ, k ∈ D τ; reason: the scaling is 'without loss of generality' (p. 10); every instance with max |w| = 1 satisfies |w| ≤ 1.
--   - reading: type set 𝒯 (finiteness implicit) → [Fintype Ty]; reason: the model is 'a finite-state Markov chain' and SPP 'a linear program' with sums over 𝒯 (pp. 9, 15); Appendix C's remark on infinitely many types presupposes finitely many in the model.
--   - generalization: φ = φ̄ and slack K/T → any φ : Ty → ℝ and any r : ℝ; reason: the decomposition uses neither; φ = φ̄, r = K/T is a special case.
--   - encoding: z^F = z^S + z^DAG as vectors → equality on the admissible entries j ∈ P τ, k ∈ D τ; reason: the LP variables are exactly these entries.
-- source:
--   Kanoria, Qian, Blind Dynamic Resource Allocation in Closed Networks via Mirror Backpressure, arXiv:1903.02764v4, Appendix A, appendix p. 3 (PDF 36), Lemma 5, (33)

import Mathlib
import Definitions.Def_MirrorBP_JEA_Model
import Definitions.Def_MirrorBP_JEA_SPP

namespace MirrorBP.JEA

open Finset

theorem lemma_5 {V Ty : Type} [Fintype V] [DecidableEq V] [Fintype Ty] [DecidableEq Ty]
    (P D : Ty → Finset V) (w : V → Ty → V → ℝ)
    (hm : 1 < Fintype.card V) (hP : ∀ τ, (P τ).Nonempty) (hD : ∀ τ, (D τ).Nonempty)
    (hw : ∀ τ, ∀ j ∈ P τ, ∀ k ∈ D τ, |w j τ k| ≤ 1)
    (φ : Ty → ℝ) (r : ℝ) (z : V → Ty → V → ℝ) (hz : relaxedFeasZ P D φ r z) :
    ∃ zS zD : V → Ty → V → ℝ,
      (∀ τ, ∀ j ∈ P τ, ∀ k ∈ D τ, z j τ k = zS j τ k + zD j τ k) ∧
      sppFeasZ P D φ zS ∧ IsAcyclicFlow P D zD ∧ relaxedFeasZ P D φ r zD := by sorry

end MirrorBP.JEA
