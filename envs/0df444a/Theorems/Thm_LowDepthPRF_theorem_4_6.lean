-- Prove2me | Theorems.Thm_LowDepthPRF_theorem_4_6
-- name    : LowDepthPRF.theorem_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:39:38.418476+00:00
-- url     : https://prove2.me/theorems/7107a47b-0c66-4ac2-adcd-47196f928907
-- title:
--   Theorem 4.6 (Main theorem) — concrete security of Construction 4.3
-- statement:
--   Let $\mathscr G$ be key-uniform with polynomially bounded input length $p$ and polynomial-size circuits, and let $H$ be a hash with polynomially bounded key length and polynomial-size circuits. For $q\in\mathbb N$ let $c_q=\lceil2\log_\Delta q\rceil$. There is a constant $c_s>0$, determined by $\mathscr G$ and $H$, such that the following holds for all $q,t,\lambda\in\mathbb N$ with $t>q^2\lambda^{c_s}$, $c_q<\ell$ and $H_\lambda$ 2-wise independent. If $G_{\lambda^{(i)}}$ is $(\Delta,t,\epsilon_i)$-weak pseudorandom for every $i\in[c_q]$, then $\mathscr F'_\lambda$ is $(q,\ t-q^2\lambda^{c_s},\ \epsilon')$-strong pseudorandom, where
--
--   $$\epsilon'=2^{-m}+\sum_{i=1}^{c_q}q\cdot m\cdot\epsilon_i,\qquad m=\lambda .$$
--
--   Weak security is needed only on the top $c_q$ levels, at security parameters $\lambda^{(i)}$ polynomially related to $\lambda$. The rest is statistical.
--
--   Differences from the source:
--   - reading: λ ≥ λ_q, the smallest λ for which Construction 4.3 is defined and c_q < ℓ → c_q < ℓ, with the construction defined by the same formulas at every λ; reason: c_q is non-increasing and ℓ non-decreasing in λ (for ℓ ≥ 1), so the set {λ | c_q < ℓ} is [λ_q, ∞)
--   - reading: c_s determined by the size of the key-uniform WPRF 𝒢; 'a 2-wise independent hashing' as a building block → ∃ c_s > 0 depending on 𝒢 and H (before q, t, λ, ε); every 2-wise independent H with polynomial-size circuits; reason: the reduction of Lemma 4.9 evaluates H (paper.md decision 8); for the paper's fixed H this is the printed statement
--   - generalization: 𝒢 a key-uniform WPRF; H 2-wise independent at every λ → 𝒢 key-uniform with polynomial-size circuits (security only through the stated hypotheses); H 2-wise independent at the λ considered; reason: the theorem's conclusion uses only these
--   - encoding: λ^{(i)} → tl λ (i − 1); reason: zero-based indexing of the tapering sequence
--   - encoding: circuits with bounded fan-in {AND, OR, NOT} gates and oracle gates, size, depth → well-formed straight-line circuits; size = number of non-input gates with an oracle gate counting 1; depth counted in gates with inputs and constants at depth 0; query count = number of oracle gates; reason: the paper fixes only the gate basis; these are the standard conventions, under which Lemma 3.12 is lossless
--   - encoding: probabilities over uniform choices of keys, inputs and functions → uniform averages over finite types (uprob); reason: every experiment of the paper samples uniformly from finite sets
-- source:
--   Ding, Jain, Komargodski, Pseudorandom Functions in NC¹ from LWE/LPN/CDH, arXiv:2608.25213 (sha256 89a55849…), Theorem 4.6, pp.18–19 (pdf 20–21)

import Mathlib
import Definitions.Def_LowDepthPRF_TaperingGGM

namespace LowDepthPRF

/-- **Theorem 4.6 (Main theorem)** (Ding, Jain, Komargodski, arXiv:2608.25213, sha256 89a55849…,
pp.18–19). Let `m, Δ, ℓ, λ^{(i)}` be as in Construction 4.3. For `q ∈ ℕ` let `c_q := ⌈2 log_Δ q⌉`
and let `λ_q` be the smallest `λ` for which Construction 4.3 is defined and `c_q < ℓ`. There
exists a constant `c_s > 0` determined by the size of the key-uniform WPRF `𝒢` such that, for any
`q, t ∈ ℕ` with `t > q² λ^{c_s}` and any `λ ≥ λ_q`: if for every `i ∈ [c_q]` the family
`G_{λ^{(i)}}` is `(Δ, t, ε_i)`-weak pseudorandom, then `ℱ′_λ` is `(q, t − q² · λ^{c_s}, ε′)`-strong
pseudorandom, where `ε′ = 2^{−m} + ∑_{i=1}^{c_q} q · m · ε_i`.

**Formalization Note.** `ℱ′_λ = constrFam G H λ` (`m = λ`), built from `𝒢` and a 2-wise
independent hash `H`. The construction is defined at every `λ`, and since `c_q` is non-increasing
and `ℓ` is non-decreasing in `λ` (for `ℓ ≥ 1`), `λ ≥ λ_q` is the condition `c_q < ℓ`. The constant
`c_s` depends on the building blocks, `𝒢` (key-uniform, input length `p` polynomially bounded,
polynomial-size circuits) and `H` (key length `kh` polynomially bounded, polynomial-size
circuits), since the reduction evaluates both; it comes before `q, t, λ, ε`. `G_{λ^{(i)}}` is
`G (tl λ (i − 1))`. Pairwise independence of `H_λ` is assumed at the `λ` considered. Every
`q ∈ ℕ` is allowed (`c_0 = c_1 = 0`). -/
theorem theorem_4_6 (p : ℕ → ℕ) (hp : PolyBounded p)
    (G : (n : ℕ) → FunFam (Fin n → Bool) (p n) (ceilSqrt n))
    (hGku : ∀ n, NWiseIndep (G n) 1) (hGeff : EfficientFam G)
    (kh : ℕ → ℕ) (hkh : PolyBounded kh)
    (H : (lam : ℕ) → FunFam (Fin (kh lam) → Bool) lam (ell lam * logDelta lam))
    (hHeff : EfficientFam H) :
    ∃ cs : ℝ, 0 < cs ∧
      ∀ (q t lam : ℕ) (ε : ℕ → ℝ),
        NWiseIndep (H lam) 2 →
        cq q lam < ell lam →
        (q : ℝ) ^ 2 * (lam : ℝ) ^ cs < t →
        (∀ i ∈ Finset.Icc 1 (cq q lam), WeakPR (G (tl lam (i - 1))) (Delta lam) t (ε i)) →
        StrongPR (constrFam G H lam) q (t - (q : ℝ) ^ 2 * (lam : ℝ) ^ cs)
          (1 / (2 : ℝ) ^ lam + ∑ i ∈ Finset.Icc 1 (cq q lam), (q : ℝ) * lam * ε i) := by sorry

end LowDepthPRF
