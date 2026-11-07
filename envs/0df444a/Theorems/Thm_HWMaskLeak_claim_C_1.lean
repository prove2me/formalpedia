-- Prove2me | Theorems.Thm_HWMaskLeak_claim_C_1
-- name    : HWMaskLeak.claim_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:32:46.890201+00:00
-- url     : https://prove2.me/theorems/4e304262-5307-4829-b2ae-fc8298c27e40
-- title:
--   Claim C.1 — a short interval $J$ with $P_J(\theta)\ll|1-2p|+|\theta|+n^{-1/2}$
-- statement:
--   There is an absolute constant $C$ such that the following holds. Let $n\ge2$, let $N$ satisfy $|N-2^n|\le2^n/n$, let $p\in[0,1]$ and let $1\le t<N$. Then there is an interval $J\subseteq\Omega=\{0,\dots,n-1\}$ of consecutive integers such that
--
--   1. $1\le\#J\le\bigl\lceil\tfrac12\log_2n\bigr\rceil$, and
--   2. $P_J(\theta)\le C\bigl(|1-2p|+|\theta|+n^{-1/2}\bigr)$ for all $|\theta|\le\pi$.
--
--   The interval does not depend on $\theta$. Its factors make the integrand of Lemma 4.11 small near $\theta=0$.
--
--   Differences from the source:
--   - encoding: an interval J ⊆ Ω; P_J(θ) ≪ … → J = Finset.Ico a b ⊆ range n; ∃ C : ℝ chosen before n, N, p, t, and J chosen before θ; reason: an interval of indices is a set of consecutive integers; the paper's ≪ is absolute and J is fixed before the ∀ θ (p.25: 'a consecutive group J, independent of θ')
--   - encoding: ⌈½ log₂ n⌉ → ⌈(Real.logb 2 n)/2⌉₊; reason: the rendered page has a ceiling (the text layer drops it)
-- source:
--   Biswas, Hwang, Maji, Shkredov, Ye, When Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding, preprint (version of October 31, 2026, sha256 ab686360…), App. C.4, Claim C.1, p.46

import Mathlib
import Definitions.Def_HWMaskLeak_PJ

namespace HWMaskLeak

/-- **Claim C.1** (Biswas, Hwang, Maji, Shkredov, Ye, *When Masks Leak Their Weight: From Additive Sharing to
Learning with Physical Rounding*, preprint (version of October 31, 2026, sha256 ab686360…), App. C.4, Claim C.1, p.46): assume `|N − 2ⁿ| ⩽ 2ⁿ/n` and `p ∈ [0, 1]`. For
`n ⩾ 2` and every `1 ⩽ t < N` there is an interval `J ⊆ Ω = {0, …, n − 1}` such that
1. `1 ⩽ #J ⩽ ⌈½ log₂ n⌉`, and
2. `P_J(θ) ≪ |1 − 2p| + |θ| + n^{−1/2}` for all `|θ| ⩽ π`.

**Formalization Note** An interval is a set of consecutive integers `Finset.Ico a b`. `≪` is an
absolute constant `C`, chosen before `n, N, p, t`; `J` depends on `n, N, p, t` but not on `θ`.
The bound on `#J` is a ceiling, `⌈(log₂ n)/2⌉₊`. -/
theorem claim_C_1 :
    ∃ C : ℝ, ∀ (n N : ℕ) [NeZero N], 2 ≤ n → |(N : ℝ) - 2 ^ n| ≤ 2 ^ n / n →
      ∀ p : ℝ, 0 ≤ p → p ≤ 1 → ∀ t : ZMod N, t ≠ 0 →
        ∃ a b : ℕ, Finset.Ico a b ⊆ Finset.range n ∧ 1 ≤ (Finset.Ico a b).card ∧
          (Finset.Ico a b).card ≤ ⌈Real.logb 2 n / 2⌉₊ ∧
          ∀ θ : ℝ, |θ| ≤ Real.pi →
            PJ p N t (Finset.Ico a b) θ ≤ C * (|1 - 2 * p| + |θ| + (n : ℝ) ^ (-(1 : ℝ) / 2)) := by sorry

end HWMaskLeak
