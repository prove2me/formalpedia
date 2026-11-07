-- Prove2me | Theorems.Thm_LowDepthPRF_corollary_4_11_main_result
-- name    : LowDepthPRF.corollary_4_11_main_result
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:38:11.898415+00:00
-- url     : https://prove2.me/theorems/ef4e8340-df3e-40dd-93b9-2a9f5dd02a6c
-- title:
--   Corollary 4.11 (Main result) — WPRFs of depth $d(\lambda)=\Omega(\log\lambda)$ give PRFs of depth $O(d(\lambda))$; WPRFs in $\mathsf{NC}^1$ give PRFs in $\mathsf{NC}^1$
-- statement:
--   Both sentences of the corollary hold.
--
--   1. Let $d:\mathbb N\to\mathbb R$ satisfy $d(\lambda)\ge c\log\lambda$ for some $c>0$ and all large $\lambda$, with $d(\lambda)/\log\lambda$ non-decreasing for $\lambda\ge2$. If there is a WPRF computable in depth $d(\lambda)$, then there is a PRF with input length $\lambda$ computable in depth $C\,d(\lambda)$ for some constant $C$.
--   2. If there is a WPRF in $\mathsf{NC}^1$, then there is a PRF with input length $\lambda$ in $\mathsf{NC}^1$.
--
--   Here a WPRF/PRF is an efficient ensemble that is weakly/strongly pseudorandom against all polynomial query and size bounds with negligible advantage. "Computable in depth $D(\lambda)$" means that, for all large $\lambda$, one circuit of polynomial size and depth at most $D(\lambda)$ computes it. $\mathsf{NC}^1$ means polynomial size and depth $O(\log\lambda)$.
--
--   This is the paper's generic, depth-preserving transformation from weak to strong PRFs. With $\mathsf{NC}^1$ WPRFs from LWE or LPN it yields $\mathsf{NC}^1$ PRFs from those assumptions.
--
--   Differences from the source:
--   - reading: there exist PRFs (Def 3.16 allows any input length p₀) → a PRF ensemble with input length p₀(λ) = λ; reason: Def 3.16 calls p₀(λ) = λ 'the usual input-length parameterization'; with p₀ free the conclusion is unconditionally true (F_k(x) = k_x on a one-bit domain is perfectly random in constant depth)
--   - generalization: WPRFs computable in depth d(λ) → depth ≤ d(λ) only for all large λ (polynomial size at every λ from efficiency); reason: a weaker hypothesis
--   - reading: computable in depth O(d(λ)); Ω(log λ); d(λ)/log λ non-decreasing → for all large λ one circuit of polynomial size and depth ≤ C·d(λ); ∃ c > 0, λ₀ with d(λ) ≥ c·log₂ λ; monotone on λ ≥ 2; reason: asymptotic notation is eventual; log 1 = 0
--   - generalization: d(·) a function of λ → d : ℕ → ℝ; reason: natural-valued d is a special case
--   - encoding: positive lengths (Def 3.16) → positive for λ ≥ 1; reason: constructions have key length λ
--   - encoding: circuits with bounded fan-in {AND, OR, NOT} gates and oracle gates, size, depth → well-formed straight-line circuits; size = number of non-input gates with an oracle gate counting 1; depth counted in gates with inputs and constants at depth 0; query count = number of oracle gates; reason: the paper fixes only the gate basis; these are the standard conventions, under which Lemma 3.12 is lossless
--   - encoding: probabilities over uniform choices of keys, inputs and functions → uniform averages over finite types (uprob); reason: every experiment of the paper samples uniformly from finite sets
-- source:
--   Ding, Jain, Komargodski, Pseudorandom Functions in NC¹ from LWE/LPN/CDH, arXiv:2608.25213 (sha256 89a55849…), Corollary 4.11, p.22 (pdf 24); informal version Theorem 1.1, p.3 (pdf 5)

import Mathlib
import Definitions.Def_LowDepthPRF_Ensemble

namespace LowDepthPRF

/-- **Corollary 4.11 (Main result)** (Ding, Jain, Komargodski, arXiv:2608.25213, sha256 89a55849…,
p.22). For any function `d(λ) = Ω(log λ)` such that `d(λ)/log λ` is non-decreasing, if there exist
WPRFs computable in depth `d(λ)`, then there exist PRFs computable in depth `O(d(λ))`. In
particular, if there exist WPRFs in NC¹, then there exist PRFs in NC¹.

**Formalization Note.**
* Both sentences are stated, as a conjunction.
* The PRF of the conclusion has input length `p₀(λ) = λ` ("the usual input-length
  parameterization", Definition 3.16). Without this, the conclusion would hold unconditionally:
  `F_k(x) = k_x` on a one-bit domain is a perfectly random function of constant depth.
  The WPRF of the hypothesis has arbitrary valid lengths.
* "Computable in depth `d(λ)`" is: efficient (part of being a (W)PRF) and, for all large `λ`, one
  circuit of polynomial size and depth `≤ d(λ)` (`DepthEventually`). `O(d(λ))` is `C·d(λ)`;
  `Ω(log λ)` is `≥ c·log₂ λ` with `c > 0` for all large `λ`; `d(λ)/log₂ λ` is non-decreasing on
  `λ ≥ 2`; `d` is real-valued.
* NC¹ is a `(poly(λ), O(log λ))`-function family ensemble (Definition 3.16). -/
theorem corollary_4_11_main_result :
    (∀ d : ℕ → ℝ,
      (∃ c : ℝ, 0 < c ∧ ∃ lam₀ : ℕ, ∀ lam ≥ lam₀, c * Real.logb 2 lam ≤ d lam) →
      MonotoneOn (fun lam : ℕ => d lam / Real.logb 2 lam) (Set.Ici 2) →
      (∃ G : Ensemble, G.IsWPRF ∧ DepthEventually G.F d) →
      ∃ F : Ensemble, (∀ lam, F.p0 lam = lam) ∧ F.IsPRF ∧
        ∃ C : ℝ, DepthEventually F.F (fun lam => C * d lam)) ∧
    ((∃ G : Ensemble, G.IsWPRF ∧ G.InNC1) →
      ∃ F : Ensemble, (∀ lam, F.p0 lam = lam) ∧ F.IsPRF ∧ F.InNC1) := by sorry

end LowDepthPRF
