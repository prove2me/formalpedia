-- Prove2me | Theorems.Thm_LowDepthPRF_corollary_4_7
-- name    : LowDepthPRF.corollary_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:39:04.839166+00:00
-- url     : https://prove2.me/theorems/f9893092-a6c2-4e4f-9f51-ecff990ef396
-- title:
--   Corollary 4.7 — a key-uniform WPRF makes $\mathscr F'$ a PRF
-- statement:
--   Let $\mathscr G=\{G_n:\{0,1\}^{p(n)}\to\{0,1\}^{\lceil\sqrt n\rceil},\ k\in\{0,1\}^n\}$ be a key-uniform WPRF. Let $H$ be a hash ensemble $\{0,1\}^\lambda\to[\Delta]^\ell$ with polynomially bounded key length and polynomial-size circuits that is 2-wise independent for all large $\lambda$. Then the ensemble $\mathscr F'$ of Construction 4.3 built from $\mathscr G$ and $H$, with input length $\lambda$, is a **PRF**: its lengths are valid, it is efficient, and for all polynomials $q,t$ there is a negligible $\epsilon$ such that $\mathscr F'_\lambda$ is $(q(\lambda),t(\lambda),\epsilon(\lambda))$-strong pseudorandom for every $\lambda$.
--
--   This is the security half of the main result.
--
--   Differences from the source:
--   - reading: ℱ′ of Construction 4.3 with 'a 2-wise independent hashing' as building block → any H with polynomial key length and circuits, 2-wise independent for all large λ (the affine hash of Lemma 4.5 is one); reason: Construction 4.3 leaves H abstract; paper.md decision 8
--   - generalization: H 2-wise independent at every λ → for all λ ≥ λ₀; reason: a weaker hypothesis; the affine hash needs ℓ log Δ ≤ λ
--   - reading: Construction 4.3 for sufficiently large λ, "finitely many smaller parameters are defined separately" → the same formulas at every λ (ℓ = 0 for λ ≤ 4); reason: the paper leaves the small-λ branch unspecified; efficiency holds at each fixed λ and the depth and security claims are asymptotic, so every choice gives the same statement
--   - encoding: key of ℱ′ as m tuples (k_G, k_XG, k_H) → a bit string of length m(λ + Σ Δ p(λ^{(i)}) + kh(λ)), decoded by a fixed permutation of positions; reason: Def 3.16 keys are bit strings
--   - encoding: circuits with bounded fan-in {AND, OR, NOT} gates and oracle gates, size, depth → well-formed straight-line circuits; size = number of non-input gates with an oracle gate counting 1; depth counted in gates with inputs and constants at depth 0; query count = number of oracle gates; reason: the paper fixes only the gate basis; these are the standard conventions, under which Lemma 3.12 is lossless
--   - encoding: probabilities over uniform choices of keys, inputs and functions → uniform averages over finite types (uprob); reason: every experiment of the paper samples uniformly from finite sets
-- source:
--   Ding, Jain, Komargodski, Pseudorandom Functions in NC¹ from LWE/LPN/CDH, arXiv:2608.25213 (sha256 89a55849…), Corollary 4.7, p.19 (pdf 21); proof in A.3, pp.37–38 (pdf 39–40)

import Mathlib
import Definitions.Def_LowDepthPRF_TaperingGGM

namespace LowDepthPRF

/-- **Corollary 4.7** (Ding, Jain, Komargodski, arXiv:2608.25213, sha256 89a55849…, p.19; proof in
A.3, pp.37–38). If `𝒢` is a key-uniform WPRF, then `ℱ′` is a PRF.

**Formalization Note.** `𝒢 = {G_n : {0,1}^{p(n)} → {0,1}^{⌈√n⌉}, k ∈ {0,1}^n}` has the shapes of
Construction 4.3. `ℱ′ = constrEnsemble G H` is Construction 4.3 with bit-string keys and input
length `λ`; "PRF" is Definition 3.17 (valid lengths, efficient, polynomially secure). The hash
`H` (Construction 4.3, building block 2) has polynomially bounded key length, polynomial-size
evaluation circuits, and is a 2-wise independent hashing for all large `λ` (the affine hash of
Lemma 4.5 is one). -/
theorem corollary_4_7 (p : ℕ → ℕ) (G : (n : ℕ) → FunFam (Fin n → Bool) (p n) (ceilSqrt n))
    (hG : (⟨p, ceilSqrt, fun n => n, G⟩ : Ensemble).IsWPRF)
    (hGku : (⟨p, ceilSqrt, fun n => n, G⟩ : Ensemble).KeyUniform)
    (kh : ℕ → ℕ) (hkh : PolyBounded kh)
    (H : (lam : ℕ) → FunFam (Fin (kh lam) → Bool) lam (ell lam * logDelta lam))
    (hHeff : EfficientFam H) (hH : ∃ lam₀ : ℕ, ∀ lam ≥ lam₀, NWiseIndep (H lam) 2) :
    (constrEnsemble G H).IsPRF := by sorry

end LowDepthPRF
