-- Prove2me | Theorems.Thm_HWMaskLeak_lemma_3_1
-- name    : HWMaskLeak.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:33:40.656165+00:00
-- url     : https://prove2.me/theorems/a13970ac-cb50-4190-9daa-0a18b7f0c44c
-- title:
--   Lemma 3.1 — $2E_k(s)\le 2\Delta_{k-1}\le F_{k-1}$
-- statement:
--   Let $N\ge2$, $k\ge2$ and $s\in G=\mathbb Z/N\mathbb Z$. Let $E_k(s)$ be the insecurity (1), $\Delta_{k-1}$ the total variation distance between the laws of $(\mathrm{wt}(X_1),\dots,\mathrm{wt}(X_{k-1}),X_1+\cdots+X_{k-1})$ and $(\mathrm{wt}(X_1),\dots,\mathrm{wt}(X_{k-1}),X_k)$ for independent uniform $X_1,\dots,X_k$, and $F_{k-1}$ the energy proxy (11). Then
--   $$
--   2E_k(s)\le 2\Delta_{k-1}\le F_{k-1}.
--   $$
--
--   The first inequality says that seeing the last share in full is at least as informative as seeing its weight; the second trades the secret-dependent $L^1$ quantity for a secret-independent $L^2$ energy, which is the starting point of every upper bound in the paper.
--
--   Differences from the source:
--   - encoding: laws of uniform random shares, total variation distance → normalized counts on finite sets and ½ Σ |P − Q| over W^k (resp. W^m × G); reason: uniform choices on finite sets are counting measures; the summation range contains both supports, so no instance changes
--   - encoding: G = ℤ/Nℤ with residues identified with {0, …, N−1} → ZMod N with [NeZero N]; reason: the hypotheses force N ≥ 1, so NeZero N excludes no instance; ZMod.val is the canonical representative
-- source:
--   Biswas, Hwang, Maji, Shkredov, Ye, When Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding, preprint (version of October 31, 2026, sha256 ab686360…), Lemma 3.1, p.18, eq. (12)

import Mathlib
import Definitions.Def_HWMaskLeak_insecurity
import Definitions.Def_HWMaskLeak_maskSumDist
import Definitions.Def_HWMaskLeak_energy

namespace HWMaskLeak

/-- **Lemma 3.1 (`E_k`-to-`F_{k−1}` reduction)** (Biswas, Hwang, Maji, Shkredov, Ye, *When Masks Leak Their Weight: From Additive Sharing to
Learning with Physical Rounding*, preprint (version of October 31, 2026, sha256 ab686360…), Lemma 3.1, p.18, eq. (12)): for every integer
`N ⩾ 2`, every `k ⩾ 2` and every secret `s ∈ G = ℤ/Nℤ`, `2E_k(s) ⩽ 2Δ_{k−1} ⩽ F_{k−1}`.

**Formalization Note** `Δ_{k−1}` is the distance (3) between the laws of
`(wt(X₁), …, wt(X_{k−1}), X₁ + ⋯ + X_{k−1})` and `(wt(X₁), …, wt(X_{k−1}), X_k)`. -/
theorem lemma_3_1 (N : ℕ) [NeZero N] (hN : 2 ≤ N) (k : ℕ) (hk : 2 ≤ k) (s : ZMod N) :
    2 * insecurity N k s ≤ 2 * maskSumDist N (k - 1) ∧
      2 * maskSumDist N (k - 1) ≤ energy N (k - 1) := by sorry

end HWMaskLeak
