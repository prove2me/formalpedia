-- Prove2me | Theorems.Thm_OptTwoSrcExt_corollary_3_32
-- name    : OptTwoSrcExt.corollary_3_32
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:26:29.542129+00:00
-- url     : https://prove2.me/theorems/4286dfea-dda0-4986-86ff-0eb8b6e959fd
-- title:
--   Corollary 3.32 — fixed-rate masks of any prescribed linear rank: bias $2^{-\theta N}$
-- statement:
--   Fix $1/2<\alpha_0<\alpha_1<1$ and $\kappa>0$. There are an integer $h\ge3$, a constant $\theta>0$ and $N_0$ such that for every $N\ge N_0$, with $K=\mathbb F_{2^N}$: for every $f:K\to K$, every $\lambda\ne0$ and every $\mu$, where $f$ is fixed-point-free or $\mu=0$, every Boolean mask $T:K\times K\to\mathbb F_2$ of global binary rank at most $\kappa N$, and all independent $U,V$ on $K$ of min-entropy at least $\alpha_1N$,
--   $$\Big|\,\mathbb E\,(-1)^{\mathrm{Tr}(\lambda(U+V)^{2^h-1}+\mu(f(U)+V)^{2^h-1})+T(U,V)}\Big|\ \le\ 2^{-\theta N}.$$
--   $\theta$ is uniform over $f,\lambda,\mu,T$.
--
--   This is the character bound behind the non-malleability of the sumset seed (Theorem 3.33): a tampered moment character stays unbiased even after adding any low-rank mask.
--
--   **Formalization Note** $K$ is `GaloisField 2 N`; the expectation is the sum over the independent product law; global rank is the binary rank of the full $K\times K$ table; $h,\theta$ are chosen before $N$. $\alpha_0$ does not occur in the conclusion and is kept as printed.
--
--   Differences from the source:
--   - reading: One can choose a fixed h (with the §3.2.11 standing assumption h ⩾ 3) → ∃ h with 3 ≤ h; reason: the standing assumption of the section in which the corollary is stated
--   - reading: every fixed-point-free f … The same conclusion for µ = 0 requires no condition on f → the hypothesis (∀ x, f x ≠ x) ∨ μ = 0; reason: the two printed cases in one hypothesis
--   - encoding: E over independent U, V; global rank → sum over the product law indepPair U V; rank2 of the full K × K table; reason: Lean convention; same instances
-- source:
--   X. Li, Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate, STOC 2027 submission (manuscript sha256 2edb00b2…), Corollary 3.32, p.47 (PDF p.49); standing assumptions of §3.2.11, p.46 (PDF p.48)

import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic
import Definitions.Def_LowErrExt_indepPair
import Definitions.Def_OptTwoSrcExt_rank2
import Definitions.Def_OptTwoSrcExt_fourier

open FuzzyExtractors.Hamming LowErrExt

namespace OptTwoSrcExt

/-- **Corollary 3.32 (Fixed-rate masks of any prescribed linear rank).**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), Corollary 3.32, printed p.47 (PDF p.49), under the
standing assumptions of §3.2.11, printed p.46 (PDF p.48) ("Fix h ⩾ 3, … K = F_{2^N}"): "Fix
1/2 < α0 < α1 < 1 and a constant κ > 0. One can choose a fixed h such that, for all sufficiently large
N, every fixed-point-free f : K → K, every λ ≠ 0, every µ, and every Boolean mask T of global rank at
most κN satisfy | E (−1)^{Tr(λ(U+V)^{2^h−1} + µ(f(U)+V)^{2^h−1}) + T(U,V)} | ⩽ 2^{−θN} for independent
U, V of min-entropy at least α1N, where θ > 0 is uniform over f, λ, µ, T. The same conclusion for µ = 0
requires no condition on f."

Given `1/2 < α₀ < α₁ < 1` and `κ > 0`, there are an integer `h ≥ 3`, a `θ > 0` and an `N₀` such that for
every `N ≥ N₀`, with `K = 𝔽_{2^N}`: for all `f : K → K`, `λ ≠ 0`, `μ ∈ K` with `f` fixed-point-free or
`μ = 0`, every Boolean mask `T : K × K → 𝔽₂` with `rank₂ T ≤ κN`, and all independent `U, V` on `K`
with min-entropy at least `α₁N`,
`|E (−1)^{Tr(λ(U + V)^{2^h − 1} + μ(f(U) + V)^{2^h − 1}) + T(U, V)}| ≤ 2^{−θN}`.

**Formalization Note.** `K` is `GaloisField 2 N`, `Tr` is `Algebra.trace (ZMod 2) K`, "global rank" is
`rank2` of the full `K × K` table, and the expectation is the sum over the independent product law.
`θ` and `h` are chosen before `N` and are uniform over `f, λ, μ, T, U, V`. `α₀` does not occur in the
conclusion; it is kept as in the printed hypotheses. `h ≥ 3` is the standing assumption of §3.2.11. -/
theorem corollary_3_32 (α₀ α₁ κ : ℝ) (h0 : 1 / 2 < α₀) (h01 : α₀ < α₁) (h1 : α₁ < 1)
    (hκ : 0 < κ) :
    ∃ h : ℕ, 3 ≤ h ∧ ∃ θ : ℝ, 0 < θ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (f : GaloisField 2 N → GaloisField 2 N) (lam μ : GaloisField 2 N)
        (T : GaloisField 2 N → GaloisField 2 N → ZMod 2),
        ((∀ x, f x ≠ x) ∨ μ = 0) → lam ≠ 0 → (rank2 T : ℝ) ≤ κ * N →
        ∀ U V : PMF (GaloisField 2 N), α₁ * N ≤ minEntropy U → α₁ * N ≤ minEntropy V →
          |∑' r : GaloisField 2 N × GaloisField 2 N, (indepPair U V r).toReal *
              signF2 (Algebra.trace (ZMod 2) (GaloisField 2 N)
                  (lam * (r.1 + r.2) ^ (2 ^ h - 1) + μ * (f r.1 + r.2) ^ (2 ^ h - 1)) +
                T r.1 r.2)| ≤ (2 : ℝ) ^ (-(θ * N)) := by sorry

end OptTwoSrcExt
