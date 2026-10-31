-- Prove2me | Theorems.Thm_MultiwayCut_lemma_2_2
-- name    : MultiwayCut.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:15:01.33439+00:00
-- url     : https://prove2.me/theorems/8de37a10-ca93-403b-b218-8d396affef7a
-- title:
--   Lemma 2.2 — CKR separates two commonly sorted points with probability at most $\sum_\ell |u_\ell-v_\ell|/\ell$
-- statement:
--   Let $\mathbf u,\mathbf v\in[0,1]^k$ with $u_1\ge\dots\ge u_k$ and $v_1\ge\dots\ge v_k$. Then the probability that the CKR algorithm assigns $\mathbf u$ and $\mathbf v$ to different terminals is at most
--   $$\sum_{\ell=1}^k\frac{|u_\ell-v_\ell|}{\ell}.$$
--
--   Applied to $f(\mathbf u),f(\mathbf v)$ for a feasible transformation $f$, it bounds the CKR part of Algorithm 3.
--
--   Differences from the source:
--   - encoding: the paper's coordinates and terminals $1,\dots,k$, $1/\ell$ → `Fin k` from $0$, $1/(\ell+1)$; reason: Lean convention; the same statement after the index shift
--   - encoding: $r\sim\mathrm{Unif}[0,1]$ and an independent uniform permutation $\sigma$ → $\frac1{k!}\sum_\sigma\lambda(\{r\in[0,1]:\dots\})$ with Lebesgue outer measure $\lambda$; reason: this is the product law written as an average over $\sigma$; Mathlib has no measurable structure on permutations
-- source:
--   Buchbinder, Schwartz & Weizman, Simplex Transformations and the Multiway Cut Problem, manuscript of Nov. 1, 2016, Lemma 2.2, p.4

import Mathlib
import Definitions.Def_MultiwayCut_CKR

namespace MultiwayCut

/-- **Lemma 2.2** (CKR), Buchbinder, Schwartz & Weizman, *Simplex Transformations and the
Multiway Cut Problem*, manuscript of Nov. 1, 2016, p.4: given `u, v ∈ [0, 1]ᵏ` with
`u₁ ≥ … ≥ u_k` and `v₁ ≥ … ≥ v_k`, the probability that `u` and `v` are assigned to different
terminals by the CKR algorithm is at most `Σ_{ℓ=1}^k |u_ℓ − v_ℓ| / ℓ`.

**Formalization Note.** Coordinates are `Fin k`, 0-based, so the paper's `1/ℓ` is
`1/(ℓ + 1)`. -/
theorem lemma_2_2 {k : ℕ} [NeZero k] (u v : Fin k → ℝ) (hu : ∀ ℓ, u ℓ ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ ℓ, v ℓ ∈ Set.Icc (0 : ℝ) 1) (hu_anti : Antitone u) (hv_anti : Antitone v) :
    sepCKR u v ≤ ∑ ℓ : Fin k, |u ℓ - v ℓ| / ((ℓ.val : ℝ) + 1) := by sorry

end MultiwayCut
