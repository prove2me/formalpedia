-- Prove2me | Theorems.Thm_LowDepthPRF_lemma_4_5
-- name    : LowDepthPRF.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:40:56.768049+00:00
-- url     : https://prove2.me/theorems/009d08d1-8fb6-427b-afa0-17e7f85aa316
-- title:
--   Lemma 4.5 — depth preserving
-- statement:
--   Let $p$ be polynomially bounded and $\mathscr G=\{G_n:\{0,1\}^{p(n)}\to\{0,1\}^{\lceil\sqrt n\rceil}\}$ with keys $\{0,1\}^n$, and let $\mathscr F'$ be Construction 4.3 built from $\mathscr G$ and the affine hash over $\mathbb F_{2^\lambda}$. Let $d(\lambda)\ge c\log\lambda$ for some $c>0$ and all large $\lambda$, with $d(\lambda)/\log\lambda$ non-decreasing on $\lambda\ge2$.
--
--   1. If $\mathscr G$ is efficient and computable in depth $d(\lambda)$, then $\mathscr F'$ is efficient and computable in depth $C\,d(\lambda)$ for some constant $C$.
--   2. If $\mathscr G$ is in $\mathsf{NC}^1$, then $\mathscr F'$ is in $\mathsf{NC}^1$.
--
--   Here "computable in depth $D(\lambda)$" means that, for all large $\lambda$, one circuit of polynomial size and depth at most $D(\lambda)$ computes the family. The tapering makes the depths of the successive WPRF calls a geometric series.
--
--   Differences from the source:
--   - reading: computed in depth d(λ); depth O(d(λ)) → efficient, and for all large λ one circuit of polynomial size and depth ≤ d(λ) (resp. ≤ C·d(λ)); reason: asymptotic statement; one circuit for size and depth (Def 3.1)
--   - reading: Construction 4.3 for sufficiently large λ, "finitely many smaller parameters are defined separately" → the same formulas at every λ (ℓ = 0 for λ ≤ 4; the affine hash pads missing bits with 0); reason: the paper leaves the small-λ branch unspecified; efficiency holds at each fixed λ and the depth and security claims are asymptotic, so every choice gives the same statement
--   - encoding: d(λ) = Ω(log λ); d(λ)/log λ non-decreasing → ∃ c > 0, λ₀ with d(λ) ≥ c·log₂ λ for λ ≥ λ₀; monotone on λ ≥ 2; reason: log 1 = 0
--   - generalization: the WPRF 𝒢 → any 𝒢 with these shapes and the depth bound (no security, no key-uniformity); reason: depth does not depend on security; a WPRF is a special case
--   - generalization: d(·) a function of λ → d : ℕ → ℝ; reason: natural-valued d is a special case
--   - encoding: the affine hash over 𝔽_{2^λ}, ℓ log Δ output bits → GaloisField 2 λ with a fixed basis; missing bits 0 when ℓ log Δ > λ; reason: the paper uses it for sufficiently large λ; any basis gives the same depth
--   - encoding: key of ℱ′ as a tuple → a bit string decoded by a fixed permutation of bit positions; reason: Def 3.16 keys are bit strings; a position permutation costs no gates
--   - encoding: circuits with bounded fan-in {AND, OR, NOT} gates and oracle gates, size, depth → well-formed straight-line circuits; size = number of non-input gates with an oracle gate counting 1; depth counted in gates with inputs and constants at depth 0; query count = number of oracle gates; reason: the paper fixes only the gate basis; these are the standard conventions, under which Lemma 3.12 is lossless
-- source:
--   Ding, Jain, Komargodski, Pseudorandom Functions in NC¹ from LWE/LPN/CDH, arXiv:2608.25213 (sha256 89a55849…), Lemma 4.5, p.18 (pdf 20)

import Mathlib
import Definitions.Def_LowDepthPRF_AffineHash

namespace LowDepthPRF

/-- **Lemma 4.5 (Depth Preserving)** (Ding, Jain, Komargodski, arXiv:2608.25213, sha256 89a55849…,
p.18). For any function `d(λ) = Ω(log λ)` such that `d(λ)/log λ` is non-decreasing, if the WPRF
`𝒢` can be computed in depth `d(λ)`, then the function family ensemble `ℱ′` defined in
Construction 4.3 can also be computed in depth `O(d(λ))`. In particular, if `𝒢` is in NC¹, then
`ℱ′` is in NC¹.

**Formalization Note.** `ℱ′` is Construction 4.3 built from `𝒢` and the affine hash of the
lemma's proof (`affineHash`, key `2λ` bits), as an ensemble with bit-string keys
(`constrEnsemble`). "Computed in depth `d(λ)`" is: efficient (polynomial size at every `λ`) and,
for all large `λ`, one circuit of polynomial size and depth `≤ d(λ)` (`DepthEventually`);
`O(d(λ))` is `C·d(λ)`. `Ω(log λ)` is `≥ c·log₂ λ` for some `c > 0` and all large `λ`; the
monotonicity of `d(λ)/log₂ λ` is required on `λ ≥ 2`. Only the depth of `𝒢` is assumed (no
security, no key-uniformity), and `p` is polynomially bounded as in Construction 4.3. -/
theorem lemma_4_5 (p : ℕ → ℕ) (hp : PolyBounded p)
    (G : (n : ℕ) → FunFam (Fin n → Bool) (p n) (ceilSqrt n)) (d : ℕ → ℝ)
    (hdΩ : ∃ c : ℝ, 0 < c ∧ ∃ lam₀ : ℕ, ∀ lam ≥ lam₀, c * Real.logb 2 lam ≤ d lam)
    (hdmono : MonotoneOn (fun lam : ℕ => d lam / Real.logb 2 lam) (Set.Ici 2)) :
    ((EfficientFam G ∧ DepthEventually G d) →
      EfficientFam (constrEnsemble G affineHash).F ∧
        ∃ C : ℝ, DepthEventually (constrEnsemble G affineHash).F (fun lam => C * d lam)) ∧
    (InNC1Fam G → InNC1Fam (constrEnsemble G affineHash).F) := by sorry

end LowDepthPRF
