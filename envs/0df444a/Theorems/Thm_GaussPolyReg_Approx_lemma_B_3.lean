-- Prove2me | Theorems.Thm_GaussPolyReg_Approx_lemma_B_3
-- name    : GaussPolyReg.Approx.lemma_B_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:41:35.642994+00:00
-- url     : https://prove2.me/theorems/16154834-0267-4691-a34a-93e2b8cb61a3
-- title:
--   Lemma B.3 — tensor-network Frobenius bound
-- statement:
--   Let $\pi$ be a finite multigraph without self-loops, and associate a symmetric tensor $T_a$ of order $\deg(a)$, with label dimension $n$, to each vertex. Sum the product of tensor entries over every edge labeling to obtain $\operatorname{val}_\pi(T)$. Then
--
--   $$|\operatorname{val}_\pi(T)|\le\prod_{a\in V(\pi)}\|T_a\|_F.$$
--
--   Parallel edges, isolated vertices, disconnected graphs and empty graphs are allowed. This controls every tensor diagram by its local tensor norms.
--
--   Differences from the source:
--   - encoding: finite multigraph with symmetric tensors indexed by incident slots → the published ContPatrol multigraph with distinct edge identifiers, and symmetric arrays on incident-endpoint subtypes; reason: orientation is a bookkeeping convention; each edge contributes one endpoint slot at each end (two at a loop), and the no-loop hypothesis gives exactly the source tensor slots while preserving parallel edges
-- source:
--   Chris Jones, Regularity lemma for Gaussian polynomials, STOC 2027 submission #1637 (October 2026), Lemma B.3, p. 18; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1637.pdf

import Mathlib
import Definitions.Def_GaussPolyReg_Approx_Tensors

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace GaussPolyReg.Approx

theorem lemma_B_3 {V E : Type} [Fintype V] [Fintype E]
    (π : Network V E) (hπ : ∀ e, π.src e ≠ π.tgt e) (n : ℕ)
    (T : (a : V) → (π.Incident a → Fin n) → ℝ) (hT : π.symmetric n T) :
    |π.value n T| ≤ π.normProduct n T := by sorry

end GaussPolyReg.Approx
