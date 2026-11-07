-- Prove2me | Theorems.Thm_LowDepthPRF_lemma_4_2
-- name    : LowDepthPRF.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:38:41.004492+00:00
-- url     : https://prove2.me/theorems/930158ad-5032-4cc4-87ae-470a761aa096
-- title:
--   Lemma 4.2 — key-uniformization
-- statement:
--   Let $d:\mathbb N\to\mathbb R$ be non-decreasing. Assume that there is a WPRF ensemble and a polynomial $t$ such that, for every $\lambda$, one circuit of size at most $t(\lambda)$ and depth at most $d(\lambda)$ computes it. Then there are a polynomially bounded $p$ and a **key-uniform** WPRF
--
--   $$\mathscr G=\bigl\{\mathscr G_\lambda=\{G_k:\{0,1\}^{p(\lambda)}\to\{0,1\}^{\lceil\sqrt\lambda\rceil},\ k\in\{0,1\}^\lambda\}\bigr\}_{\lambda},$$
--
--   with a constant $c$ and a polynomial $t'$ such that, for every $\lambda$, one circuit of size at most $t'(\lambda)$ and depth at most $d(\lambda)+c$ computes $\mathscr G_\lambda$.
--
--   This produces the building block of Construction 4.3 from an arbitrary WPRF, at a constant additive cost in depth.
--
--   Differences from the source:
--   - reading: a depth-d WPRF; depth-(d + O(1)) → a WPRF that is a (t, d)-ensemble with t a polynomial, for every λ; depth ≤ d(λ) + c for every λ with the same circuit of polynomial size; reason: Def 3.16's (t, d)-function family ensemble, for every λ
--   - generalization: d(·) a function of λ → d : ℕ → ℝ; reason: natural-valued d is a special case
--   - encoding: positive lengths (Def 3.16) → positive for λ ≥ 1; reason: the key length is λ, which is 0 at λ = 0
--   - encoding: circuits with bounded fan-in {AND, OR, NOT} gates and oracle gates, size, depth → well-formed straight-line circuits; size = number of non-input gates with an oracle gate counting 1; depth counted in gates with inputs and constants at depth 0; query count = number of oracle gates; reason: the paper fixes only the gate basis; these are the standard conventions, under which Lemma 3.12 is lossless
--   - encoding: probabilities over uniform choices of keys, inputs and functions → uniform averages over finite types (uprob); reason: every experiment of the paper samples uniformly from finite sets
-- source:
--   Ding, Jain, Komargodski, Pseudorandom Functions in NC¹ from LWE/LPN/CDH, arXiv:2608.25213 (sha256 89a55849…), Lemma 4.2, p.16 (pdf 18); proof in A.2, pp.36–37 (pdf 38–39)

import Mathlib
import Definitions.Def_LowDepthPRF_TaperingGGM

namespace LowDepthPRF

/-- **Lemma 4.2 (Key-uniformization)** (Ding, Jain, Komargodski, arXiv:2608.25213, sha256
89a55849…, p.16; proof in A.2, pp.36–37). Let `d(·)` be a non-decreasing function of `λ`. Assume
there exists a depth-`d` WPRF. Then there exists a depth-`(d + O(1))` key-uniform WPRF
`𝒢 = {𝒢_λ = {G_k : {0,1}^{p(λ)} → {0,1}^{⌈√λ⌉}, k ∈ {0,1}^λ}}`, where `p(λ)` is polynomially
bounded.

**Formalization Note.** "Depth-`d` WPRF": a WPRF ensemble (arbitrary lengths) that is a
`(t, d)`-function family ensemble for a polynomial `t`, i.e. for every `λ` one circuit of size
`≤ t(λ)` and depth `≤ d(λ)` (Definition 3.16). The conclusion has the same form with
`d(λ) + c` for a constant `c` (`d + O(1)`), with the exact lengths `p(λ)`, `⌈√λ⌉`, `λ`. `d` is
real-valued. -/
theorem lemma_4_2 (d : ℕ → ℝ) (hd : Monotone d)
    (hG : ∃ G : Ensemble, G.IsWPRF ∧
      ∃ t : Polynomial ℕ, ∀ lam, IsSizeDepth (G.F lam) ((t.eval lam : ℕ) : ℝ) (d lam)) :
    ∃ p : ℕ → ℕ, PolyBounded p ∧
      ∃ G' : (lam : ℕ) → FunFam (Fin lam → Bool) (p lam) (ceilSqrt lam),
        (⟨p, ceilSqrt, fun lam => lam, G'⟩ : Ensemble).IsWPRF ∧
        (⟨p, ceilSqrt, fun lam => lam, G'⟩ : Ensemble).KeyUniform ∧
        ∃ c : ℝ, ∃ t : Polynomial ℕ,
          ∀ lam, IsSizeDepth (G' lam) ((t.eval lam : ℕ) : ℝ) (d lam + c) := by sorry

end LowDepthPRF
