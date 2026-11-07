-- Prove2me | Theorems.Thm_LowDepthPRF_lemma_4_9
-- name    : LowDepthPRF.lemma_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:39:55.17862+00:00
-- url     : https://prove2.me/theorems/057b2513-a2f1-48d0-a2bd-ed260bbdde9c
-- title:
--   Lemma 4.9 — one computational hybrid step $\mathbf H_{1,m',j}\approx\mathbf H_{1,m',j+1}$
-- statement:
--   Let $\mathscr G$ (input length $p$) and the hash $H$ (key length $kh$) have polynomially bounded lengths and polynomial-size evaluation circuits. There is a constant $c_s>0$, depending only on $\mathscr G$ and $H$, such that the following holds. Let $q,t,\lambda\in\mathbb N$ with $c_q=\lceil2\log_\Delta q\rceil<\ell$ and $t>q^2\lambda^{c_s}$, let $m'\in[m]$ with $m=\lambda$, and let $j\in\{0,\dots,c_q-1\}$. If $G_{\lambda^{(j+1)}}$ is $(\Delta,t,\epsilon_{j+1})$-weak pseudorandom, then the games
--
--   $$\mathbf H_{1,m',j}\ \text{and}\ \mathbf H_{1,m',j+1}\ \text{are}\ \bigl(q,\ t-q^2\lambda^{c_s},\ q\,\epsilon_{j+1}\bigr)\text{-indistinguishable}.$$
--
--   Each step replaces one more level of one tree by a truly random function. This is the only place the proof uses the computational security of $\mathscr G$.
--
--   Differences from the source:
--   - reading: the setting of Theorem 4.6's proof ('Fix q, t ∈ ℕ and fix any λ such that c_q < ℓ'; c_s 'determined by the size of the key-uniform WPRF 𝒢') → self-contained, with ∃ c_s > 0 depending on 𝒢 and H, quantified before q, t, λ, m′, j, ε; reason: the reduction D′ also evaluates H (paper.md decision 8); for the paper's fixed H this is the printed statement
--   - generalization: the hypotheses of Theorem 4.6 (𝒢 a key-uniform WPRF, all levels i ∈ [c_q] weakly pseudorandom) → only G_{λ^{(j+1)}} (Δ, t, ε_{j+1})-weak pseudorandom; 𝒢 and H efficient; reason: the step uses only that level's security
--   - encoding: TGGM_(0) with y^{(1)} ← k_G → R on the empty prefix as the root key; reason: a uniform R : [Δ]^0 → {0,1}^λ is a uniform k_G; the paper reads it the same way in Lemma 4.10
--   - encoding: circuits with bounded fan-in {AND, OR, NOT} gates and oracle gates, size, depth → well-formed straight-line circuits; size = number of non-input gates with an oracle gate counting 1; depth counted in gates with inputs and constants at depth 0; query count = number of oracle gates; reason: the paper fixes only the gate basis; these are the standard conventions, under which Lemma 3.12 is lossless
--   - encoding: probabilities over uniform choices of keys, inputs and functions → uniform averages over finite types (uprob); reason: every experiment of the paper samples uniformly from finite sets
-- source:
--   Ding, Jain, Komargodski, Pseudorandom Functions in NC¹ from LWE/LPN/CDH, arXiv:2608.25213 (sha256 89a55849…), Lemma 4.9, p.19 (pdf 21), in the proof of Theorem 4.6 (pp.19–22)

import Mathlib
import Definitions.Def_LowDepthPRF_HybridFamily

namespace LowDepthPRF

/-- **Lemma 4.9** (Ding, Jain, Komargodski, arXiv:2608.25213, sha256 89a55849…, p.19). In the proof
of Theorem 4.6 (fix `q, t ∈ ℕ` and `λ` with `c_q < ℓ`; `c_s` is the constant of Theorem 4.6, with
`t > q² λ^{c_s}`): for every `m′ ∈ [m]` and every `j ∈ {0, …, c_q − 1}`, the games `H_{1,m′,j}`
and `H_{1,m′,j+1}` are `(q, t − q² · λ^{c_s}, q ε_{j+1})`-indistinguishable.

**Formalization Note.** Self-contained form. The building blocks are `𝒢` (input length `p(n)`
polynomially bounded, polynomial-size evaluation circuits) and the hash `H` (key length `kh`
polynomially bounded, polynomial-size evaluation circuits); `c_s > 0` is existential, depends only
on them, and comes before `q, t, λ, m′, j, ε`. `H_{1,m′,j}` is the strong real game of
`ℱ′_{(m′,j)}` (`hybridFam`), with `m = λ`. The only computational hypothesis used by the lemma is
stated: `G_{λ^{(j+1)}}` (= `G (tl λ j)`) is `(Δ, t, ε_{j+1})`-weak pseudorandom; neither
key-uniformity nor pairwise independence is assumed. -/
theorem lemma_4_9 (p : ℕ → ℕ) (hp : PolyBounded p)
    (G : (n : ℕ) → FunFam (Fin n → Bool) (p n) (ceilSqrt n)) (hGeff : EfficientFam G)
    (kh : ℕ → ℕ) (hkh : PolyBounded kh)
    (H : (lam : ℕ) → FunFam (Fin (kh lam) → Bool) lam (ell lam * logDelta lam))
    (hHeff : EfficientFam H) :
    ∃ cs : ℝ, 0 < cs ∧
      ∀ (q t lam : ℕ) (ε : ℕ → ℝ),
        cq q lam < ell lam →
        (q : ℝ) ^ 2 * (lam : ℝ) ^ cs < t →
        ∀ m' ∈ Finset.Icc 1 lam, ∀ j < cq q lam,
          WeakPR (G (tl lam j)) (Delta lam) t (ε (j + 1)) →
          Indist (strongReal (hybridFam G H q lam m' j))
            (strongReal (hybridFam G H q lam m' (j + 1))) q
            (t - (q : ℝ) ^ 2 * (lam : ℝ) ^ cs) (q * ε (j + 1)) := by sorry

end LowDepthPRF
