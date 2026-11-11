-- Prove2me | Theorems.Thm_InducedExpanderTest989_Structural_lemma_4_10
-- name    : InducedExpanderTest989.Structural.lemma_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T22:00:42.931457+00:00
-- url     : https://prove2.me/theorems/07f5ba15-fdbc-49c8-a32a-bb08e9690ec0
-- title:
--   Lemma 4.10 — separation of conditional scores
-- statement:
--   Let G have degree bound d≥1, 0<α,ϕ≤1, 3/4≤κ<1 and n≥4/((1−κ)α). Set all parameters as in Algorithm 1, β=(1−κ)α, L=⌊log₂(1/(α−β))⌋+1 and ψ=αβ/(64·1089ΛℓL). Choose a uniform anchor x and conditionally m_A independent samples A from q_x=e_xQ_ℓ. Its score f(x,A) is the probability of intersection with a fresh independent uniform partner and its m_D endpoint samples. Then
--   $$G\in P_{\alpha,\phi}\ \Longrightarrow\ \Pr[f(x,A)\ge\alpha-\beta/4]\ge\tfrac{15}{16}(\alpha-\beta/8),$$
--   $$G\notin P_{\alpha-\beta,\psi}\ \Longrightarrow\ \Pr[f(x,A)>\alpha-3\beta/4]\le\alpha/16.$$
--   The probabilities average over both x and A, keeping their dependence. Both clauses use the same explicit ψ.
--
--   Differences from the source:
--   - encoding: vertices [n], slots [d], null symbol ⊥ → Fin n, zero-based Fin d slots, none; reason: renumbering preserves every adjacency list and graph
--   - encoding: real parameters, natural logarithms and integer ceilings → Real.log, Real.sqrt, Nat.ceil and real powers; reason: all arguments have their stated positive domains; Nat.ceil agrees with the paper on those domains
--   - encoding: probabilities over x uniform and A conditional on x → finite sums of the uniform and iid product weights; reason: the score averages only fresh partner randomness while the event probability averages anchor randomness
-- source:
--   Pan Peng, Ranran Shen, Testing for a Large Induced Expander: Sublinear Algorithms and Query Lower Bounds, STOC 2027 submission #989 (October 2026), source.pdf SHA-256 98b4035a0ac121d1c1bfb6abdeb3cdb6cf3304ef3cb21b2cd58c97e4bbce6334, p.29 (PDF p.31), Lemma 4.10; (19) p.28 and (21) p.30; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/989.pdf

import Mathlib
import Definitions.Def_InducedExpanderTest989_Structural_Algorithm

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal
noncomputable section

namespace InducedExpanderTest989.Structural

theorem lemma_4_10 {n d : ℕ} (hd : 1 ≤ d) (G : SimpleGraph (Fin n))
    (hG : DegreeBound d G) (α κ ϕ : ℝ) (hp : BaseParams α κ ϕ)
    (hn : LargeEnough n α κ) :
    let Q := averaging (graphWalk d G) (window n α κ ϕ)
    let a := anchorsLength n α κ
    let b := partnersLength n α κ
    (HasCore d G α ϕ → (15/16 : ℝ) * (α-beta α κ/8) ≤
      anchorEventProb Q a b (fun z => α-beta α κ/4 ≤ z)) ∧
    (¬ HasCore d G (α-beta α κ) (psi n α κ ϕ) →
      anchorEventProb Q a b (fun z => α-3*beta α κ/4 < z) ≤ α/16) := by sorry

end InducedExpanderTest989.Structural
