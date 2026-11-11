-- Prove2me | Theorems.Thm_InducedExpanderTest989_Structural_lemma_4_6
-- name    : InducedExpanderTest989.Structural.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T22:00:19.175359+00:00
-- url     : https://prove2.me/theorems/480454e5-34dc-4a2a-bc85-6d13fec488b3
-- title:
--   Lemma 4.6 — relative transfer with a slack-controlled exceptional set
-- statement:
--   Let G have degree bound d≥1, 0<α,ϕ≤1, 3/4≤κ<1, n≥4/((1−κ)α), and β=(1−κ)α. Suppose U has |U|≥αn and Φ_in(G[U])≥ϕ. With t,c_exc,ℓ set as in Algorithm 1 and q_x=e_xQ_ℓ, there exists a set 𝒢⊆U such that
--   $$|\mathcal G|\ge(\alpha-\beta/8)n,\qquad
--   \|q_x-\pi_UQ_\ell\|_{\rm TV}\le1/8\quad(x\in\mathcal G),$$
--   and, for all x,y∈𝒢,
--   $$\|q_x-q_y\|_{\rm TV}\le1/4.$$
--   The common law may place mass outside U. The exceptional size is controlled by β, not by the size of the exterior.
--
--   Differences from the source:
--   - encoding: vertices [n], slots [d], null symbol ⊥ → Fin n, zero-based Fin d slots, none; reason: renumbering preserves every adjacency list and graph
--   - encoding: real parameters, natural logarithms and integer ceilings → Real.log, Real.sqrt, Nat.ceil and real powers; reason: all arguments have their stated positive domains; Nat.ceil agrees with the paper on those domains
-- source:
--   Pan Peng, Ranran Shen, Testing for a Large Induced Expander: Sublinear Algorithms and Query Lower Bounds, STOC 2027 submission #989 (October 2026), source.pdf SHA-256 98b4035a0ac121d1c1bfb6abdeb3cdb6cf3304ef3cb21b2cd58c97e4bbce6334, p.21 (PDF p.23), Lemma 4.6; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/989.pdf

import Mathlib
import Definitions.Def_InducedExpanderTest989_Structural_Algorithm

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal
noncomputable section

namespace InducedExpanderTest989.Structural

theorem lemma_4_6 {n d : ℕ} (hd : 1 ≤ d) (G : SimpleGraph (Fin n))
    (hG : DegreeBound d G) (α κ ϕ : ℝ) (hp : BaseParams α κ ϕ)
    (hn : LargeEnough n α κ) (U : Finset (Fin n))
    (hu : α * n ≤ (U.card : ℝ)) (hc : ϕ ≤ innerConductance d G U) :
    ∃ good : Finset (Fin n), good ⊆ U ∧
      (α - beta α κ / 8) * n ≤ (good.card : ℝ) ∧
      (∀ x ∈ good, MarkovChain.tvDist
        ((averaging (graphWalk d G) (window n α κ ϕ)) x)
        (Matrix.vecMul (uniformOn U) (averaging (graphWalk d G) (window n α κ ϕ))) ≤ 1/8) ∧
      ∀ x ∈ good, ∀ y ∈ good, MarkovChain.tvDist
        ((averaging (graphWalk d G) (window n α κ ϕ)) x)
        ((averaging (graphWalk d G) (window n α κ ϕ)) y) ≤ 1/4 := by sorry

end InducedExpanderTest989.Structural
